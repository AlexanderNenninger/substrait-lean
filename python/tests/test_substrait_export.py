"""`Report.to_substrait` and `sv.Report.from_substrait` (#664): the export of a
verified plan for any Substrait consumer, with its contract as metadata.

The round trips export, read back and prove the contract again."""

from __future__ import annotations

import functools
import json
import math
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


ASCII_S = ~_.s.re_search(r"[^\x00-\x7f]")  # the condition D43's guards ask for


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
    assert m["semantics"] == "portable"
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
    # The `+ 0.0` shims the export writes for double keys cannot overflow
    # (`BinFn.shrinks_fin`), so the import proves what the export did.
    assert again.verdict == report.verdict
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
    with pytest.raises(ExportError, match="semantics='portable'"):
        report.to_substrait()


def test_st10_refuses_in_every_mode() -> None:
    t = ibis.table({"s": "string"}, name="t")
    report = _verify(t.select(u=_.s.upper()), {"t": [ASCII_S]})
    for mode in se.SHIMS:
        with pytest.raises(ExportError, match="ST-10"):
            report.to_substrait(shims=mode)


def test_function_outside_the_yamls_is_refused() -> None:
    t = ibis.table({"s": "string"}, name="t")
    report = _verify(t.select(h=_.s.levenshtein("a")), {"t": [ASCII_S]})
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


@functools.cache
def _gap_report(case: str) -> sv.Report:
    """The case's report, verified once for the three modes (an export does not
    change it)."""
    expr, requires, _ = GAP_CASES[case]
    return _verify(expr, requires)


@pytest.mark.parametrize("case", list(GAP_CASES))
def test_apply_rewrites_the_gap(case: str) -> None:
    option = GAP_CASES[case][2]
    m = read(_gap_report(case).to_substrait(shims="apply")).manifest
    # D30: a consumer's own variance is within the plan's bound of the
    # reference's exact moments rounded once, and a consumer's double keys
    # pick a member of a zero's class, which the default observation reads as one.
    assert m["class"] == "observed"
    assert any(s["option"] == option for s in m["shims"]), m["shims"]
    assert not m["assumptions"]


@pytest.mark.parametrize("case", list(GAP_CASES))
def test_annotate_ships_the_assumption(case: str) -> None:
    option = GAP_CASES[case][2]
    report = _gap_report(case)
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
    gap = "ST-3" if GAP_CASES[case][2] == "stat_degenerate" else "ST-4"
    with pytest.raises(ExportError, match=re.escape(f"({gap}, upstream/bugs/{gap}.json)")):
        _gap_report(case).to_substrait(shims="refuse")


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


RP = ibis.table({"a": "int64", "b": "int64"}, name="p")


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_report_read_back_checks_a_composite_foreign_key(engine):
    """The key's parts travel together and are checked together: (1, 5) has
    each part in `p`, in different rows (#2223)."""
    fk = sv.references("id", "amt", to=("p", ["a", "b"]))
    report, back = _imported([fk], [], RO.join(RP, RO.id == RP.a).select(RO.id))
    assert fk in back._conditions["o"]
    p = pa.table({"a": pa.array([1, 2], pa.int64()), "b": pa.array([6, 5], pa.int64())})
    bad = _o([(1, 5)])
    put_table(bad, "p", p)
    for r in (report, back):
        with pytest.raises(PreconditionError, match="refused before the run"):
            r.run(bad, engine)
    good = _o([(1, 6), (3, None)])
    put_table(good, "p", p)
    assert back.run(good, engine).num_rows == 1


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


def test_a_text_fact_travels_and_is_checked_on_read_back() -> None:
    """A text column's inferred fact (`reverse` needs ASCII, D43) has no
    plan of its own: the export records it as a `text` precondition, the
    read-back proves again with it and checks it on the data (#862)."""
    S = ibis.table({"s": "string"}, name="s")
    report = sv.verify(S.select(r=S.s.reverse()), on_inferred="warn")
    back = sv.Report.from_substrait(report.to_substrait(format="binary"))
    assert back.verdict == report.verdict == sv.Verdict.PROVED
    (fact,) = read(report.to_substrait()).requires
    assert fact["kind"] == "text" and fact["entry"]["fact"] == "ascii"
    con = connect()
    put_table(con, "s", pa.table({"s": ["abc", "äbc"]}))
    with pytest.raises(PreconditionError, match="refused before the run"):
        back.run(con, "duckdb")


# -- ST-4: the ordering comparisons of doubles (#741) ----------------------------------

ORDERINGS = {
    "gt": orders.filter(orders.x > 1.0).select("id"),
    "gte": orders.filter(orders.x >= 1.0).select("id"),
    "lt": orders.filter(orders.x < orders.amount).select("id"),
    "lte": orders.filter(orders.x <= 1.0).select("id"),
    "between": orders.filter(orders.x.between(0.0, 2.0)).select("id"),
}


@pytest.mark.parametrize("case", list(ORDERINGS))
def test_an_ordering_comparison_of_doubles_exports(case: str) -> None:
    report = _verify(ORDERINGS[case], BOUNDED)
    m = read(report.to_substrait()).manifest
    assert any(s["option"] in ("nan_order", "nan_equality", "zero_sign") for s in m["shims"]), m
    assert not m["assumptions"]
    assert "is_nan" in json.dumps(read(report.to_substrait()).plan)
    back = sv.Report.from_substrait(report.to_substrait())
    assert back.verdict in (sv.Verdict.PROVED, sv.Verdict.PROVED_WITH_CHECKS)
    with pytest.raises(ExportError, match="ST-4"):
        report.to_substrait(shims="refuse")


def _evaluate(plan: dict, e: dict, row: tuple):
    """The shim's expressions under SQL's three-valued logic, doubles as IEEE 754 has them
    and `lt` as a consumer gives it (False when a side is NaN)."""
    names = {
        x["extensionFunction"]["functionAnchor"]: x["extensionFunction"]["name"]
        for x in plan["extensions"]
    }
    if "selection" in e:
        # Substrait's JSON leaves out a field of 0.
        return row[e["selection"]["directReference"]["structField"].get("field", 0)]
    if "literal" in e:
        return None if "null" in e["literal"] else float(e["literal"]["fp64"])
    if "ifThen" in e:
        (arm,) = e["ifThen"]["ifs"]
        pick = arm["then"] if _evaluate(plan, arm["if"], row) else e["ifThen"]["else"]
        return _evaluate(plan, pick, row)
    f = e["scalarFunction"]
    a = [_evaluate(plan, x["value"], row) for x in f["arguments"]]
    match names[f["functionReference"].__int__()].split(":")[0]:
        case "is_nan":
            return None if a[0] is None else a[0] != a[0]
        case "is_null":
            return a[0] is None
        case "not":
            return None if a[0] is None else not a[0]
        case "add":
            return None if None in a else a[0] + a[1]
        case "lt":
            return None if None in a else a[0] < a[1]
        case "gte":
            return None if None in a else a[0] >= a[1]
        case "floor" | "ceil" if a[0] is None or not math.isfinite(a[0]):
            return a[0]
        case "floor":
            return float(math.floor(a[0]))
        case "ceil":
            return float(math.ceil(a[0]))
        case "and":
            return False if False in a else None if None in a else True
        case "or":
            return True if True in a else None if None in a else False
    raise AssertionError(names)


@pytest.mark.parametrize("name", ["lt", "gt", "lte", "gte"])
def test_the_ordering_shim_is_three_valued_over_the_special_doubles(name: str) -> None:
    """NaN greatest, one zero, NULL when a side is NULL: the cross product of NaN, NULL, the
    infinities, the zeros and a number."""
    from sverify._substrait_shims import Builder, ordering

    plan: dict = {}
    b = Builder(plan)
    expr = ordering(b, name, b.field(0), b.field(1))
    ref = {
        "lt": lambda x, y: x < y,
        "gt": lambda x, y: x > y,
        "lte": lambda x, y: x <= y,
        "gte": lambda x, y: x >= y,
    }[name]

    def key(v):  # NaN greatest
        return (v != v, 0.0 if v != v else v + 0.0)

    values = SPECIAL
    for x in values:
        for y in values:
            want = None if x is None or y is None else ref(key(x), key(y))
            assert _evaluate(plan, expr, (x, y)) is want, (name, x, y)


SPECIAL = [None, NAN, float("-inf"), -1.0, -0.0, 0.0, 1.0, float("inf")]
PAIRS = [(a, b) for a in SPECIAL for b in SPECIAL]
PAIR_ROWS = pa.table(
    {
        "i": pa.array(range(len(PAIRS)), pa.int64()),
        "a": pa.array([a for a, _ in PAIRS], pa.float64()),
        "b": pa.array([b for _, b in PAIRS], pa.float64()),
    }
)
PT = ibis.table({"i": "int64", "a": "float64", "b": "float64"}, name="t")
COMPARISONS = {
    "lt": lambda: PT.a < PT.b,
    "le": lambda: PT.a <= PT.b,
    "gt": lambda: PT.a > PT.b,
    "ge": lambda: PT.a >= PT.b,
    "between_value": lambda: PT.a.between(PT.b, 1.0),
    "between_low": lambda: PT.a.between(-1.0, PT.b),
    "between_high": lambda: PT.b.between(PT.a, 1.0),
}


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("case", list(COMPARISONS))
def test_the_exported_ordering_agrees_with_the_reference_on_an_engine(
    case: str, engine: str
) -> None:
    """#741: over NULL, NaN, -inf, -1, -0, +0, 1 and +inf, all 64 ordered pairs (and, for
    `between`, each pair as the value and one bound), the plan read back from the export,
    run on the engine, gives the reference's values. The export carries the shim, and the
    read-back keeps it."""
    pytest.importorskip(engine)
    report = _verify(PT.select("i", c=COMPARISONS[case]()), counterexamples=0)
    exported = report.to_substrait()
    assert "is_nan" in json.dumps(read(exported).plan)
    back = sv.Report.from_substrait(exported)
    assert "is_nan" in json.dumps(back.internal_plan, default=str)
    con = connect()
    put_table(con, "t", PAIR_ROWS)
    want = report.run(con, engine).sort_by("i").column("c").to_pylist()
    got = back.run(con, engine).sort_by("i").column("c").to_pylist()
    assert got == want


def test_set_inputs_of_two_decimal_precisions_are_cast_to_one() -> None:
    """A full outer join of two sums is written as a set relation whose inputs
    differ in decimal precision, which Substrait does not allow: the export
    casts the narrower input to the wider precision, at the same scale, and
    the plan reads back with the same verdict (#1904)."""
    a = ibis.table({"k": "int64", "d": "decimal(10,2)"}, name="a")
    b = ibis.table({"k": "int64", "d": "decimal(12,2)"}, name="b")
    ga, gb = (t.group_by("k").agg(s=t.d.sum()) for t in (a, b))
    report = _verify(ga.outer_join(gb, "k").select(ga.k, x=ga.s, y=gb.s))
    plan = report.to_substrait(shims="annotate")
    rel = json.loads(plan)["relations"][0]["root"]["input"]
    while "set" not in rel:
        [(_, body)] = rel.items()
        rel = body["input"]
    assert any("project" in i for i in rel["set"]["inputs"])
    assert sv.Report.from_substrait(plan).verdict == report.verdict


# -- the shims a consumer runs, on an engine (#750) -------------------------------------

KT = ibis.table({"i": "int64", "a": "float64", "b": "float64", "g": "int64"}, name="kt")
_KEYS = [NAN, -0.0, 0.0, 1.5, -1.5, NAN, 1.5, None, float("inf"), float("-inf")]
KEY_ROWS = pa.table(
    {
        "i": pa.array(range(len(_KEYS)), pa.int64()),
        "a": pa.array(_KEYS, pa.float64()),
        "b": pa.array(list(reversed(_KEYS)), pa.float64()),
        "g": pa.array([i % 3 for i in range(len(_KEYS))], pa.int64()),
    }
)
VT = ibis.table({"i": "int64", "a": "float64", "g": "int64"}, name="vt")
_VALUES = [-0.0, 0.0, 1.5, -1.5, 2.5, -2.5, 0.5, -0.5, 99.9, -99.9, 7.0]
VALUE_ROWS = pa.table(
    {
        "i": pa.array(range(len(_VALUES)), pa.int64()),
        "a": pa.array(_VALUES, pa.float64()),
        # Groups of 2, 3, 4, 1 and 1 rows: a group of one is too few for SAMPLE.
        "g": pa.array([0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 4], pa.int64()),
    }
)
FINITE_A = {"vt": [_.a.notnull(), ~_.a.isnan(), _.a >= -100.0, _.a <= 100.0]}

#: Each shim's plan, the table it reads, its rows and the option its shim writes away.
SHIMMED = {
    "a double key": (KT.group_by("a").agg(n=_.i.count()), "kt", None, "nan_equality"),
    "a double key beside an integer": (
        KT.group_by(["g", "a"]).agg(n=_.i.count(), s=_.i.sum()),
        "kt",
        None,
        "nan_equality",
    ),
    "equal": (KT.filter(KT.a == KT.b).select("i"), "kt", None, "nan_equality"),
    "not equal": (KT.filter(KT.a != KT.b).select("i"), "kt", None, "nan_equality"),
    "variance": (VT.group_by("g").agg(v=_.a.var()), "vt", FINITE_A, "stat_degenerate"),
    "POPULATION": (
        VT.group_by("g").agg(v=_.a.var(how="pop")),
        "vt",
        FINITE_A,
        "stat_degenerate",
    ),
    "a filtered variance": (
        VT.group_by("g").agg(v=_.a.var(where=_.i > 3)),
        "vt",
        FINITE_A,
        "stat_degenerate",
    ),
    "std_dev beside another measure": (
        VT.group_by("g").agg(n=_.i.count(), s=_.a.std(), t=_.i.sum()),
        "vt",
        FINITE_A,
        "stat_degenerate",
    ),
    "no key": (VT.aggregate(v=VT.a.var(), n=VT.i.count()), "vt", FINITE_A, "stat_degenerate"),
}


def _same_rows(got: pa.Table, want: pa.Table) -> bool:
    """The same rows in any order, NaN equal to NaN, and doubles equal within a
    relative 1e-12: the class is `observed`, so a consumer's variance may differ
    in its last bits (D30)."""

    def key(r: dict) -> str:
        return json.dumps({k: round(v, 6) if isinstance(v, float) else v for k, v in r.items()})

    def same(a: object, b: object) -> bool:
        if isinstance(a, float) and isinstance(b, float):
            return (a != a and b != b) or a == b or abs(a - b) <= 1e-12 * max(abs(a), abs(b))
        return a == b

    g, w = (sorted(t.to_pylist(), key=key) for t in (got, want))
    return len(g) == len(w) and all(
        r.keys() == q.keys() and all(same(r[k], q[k]) for k in r) for r, q in zip(g, w, strict=True)
    )


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("case", list(SHIMMED))
def test_a_shimmed_plan_gives_the_reference_s_rows_on_an_engine(case: str, engine: str) -> None:
    """The plan `shims="apply"` writes, read back and run on the engine, gives
    what the verified plan gives there: the shim rewrites the plan and keeps
    its meaning, over NaN, both zeros, NULL and the infinities as keys, and
    groups too small for a variance."""
    pytest.importorskip(engine)
    expr, name, requires, option = SHIMMED[case]
    report = _verify(expr, requires, counterexamples=0)
    exported = report.to_substrait(shims="apply")
    m = read(exported).manifest
    assert any(s["option"] == option for s in m["shims"]), m["shims"]
    assert not m["assumptions"]
    back = sv.Report.from_substrait(exported)
    con = connect()
    put_table(con, name, KEY_ROWS if name == "kt" else VALUE_ROWS)
    want, got = report.run(con, engine), back.run(con, engine)
    assert got.schema.names == want.schema.names
    assert _same_rows(got, want), (got.to_pylist(), want.to_pylist())


def test_the_variance_shim_counts_what_the_variance_reads() -> None:
    """ST-3's count reads the variance's argument, under its filter and
    invocation, and the threshold follows the distribution: 2 for SAMPLE, 1
    for POPULATION."""
    for expr, threshold in (
        (VT.group_by("g").agg(v=_.a.var(where=_.i > 3)), "2"),
        (VT.group_by("g").agg(v=_.a.var(how="pop")), "1"),
    ):
        plan = read(_verify(expr, FINITE_A).to_substrait(shims="apply")).plan
        text = json.dumps(plan)
        assert '"count' in text and f'"i64": "{threshold}"' in text
        if threshold == "2":
            # The count keeps the variance's filter.
            assert text.count('"filter"') >= 2


def _typed(expr, requires=None):
    """The written plan of a verified `expr`, typed, and a builder for shims."""
    import copy

    from sverify._substrait_shims import Builder

    report = _verify(expr, requires, counterexamples=0)
    plan = copy.deepcopy(read(report.to_substrait(shims="annotate")).plan)
    typer = se._Typer(plan)
    typer.run()
    return typer, Builder(plan)


def test_st4_puts_nan_first_in_a_double_sort_key() -> None:
    """ST-4 on a sort of doubles: the key `is_nan(x)` and then `x + 0.0`, so
    NaN sorts greatest (in the key's direction) and the two zeros tie."""
    from sverify._substrait_shims import st4

    typer, b = _typed(KT.order_by([ibis.desc("a"), "i"]).select("i", "a"))
    out = st4(typer, b)
    assert out is not None and "sort key of doubles" in out["shim"]
    [sorts] = _find(typer.plan, "sorts")
    assert len(sorts) == 3
    first, second, third = sorts
    # The NaN test sorts in the key's own direction, ahead of the key.
    assert first["direction"] == second["direction"] != third["direction"]
    names = {
        e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"]
        for e in typer.plan["extensions"]
    }
    assert names[first["expr"]["scalarFunction"]["functionReference"]] == "is_nan"
    assert names[second["expr"]["scalarFunction"]["functionReference"]] == "add"
    assert "_before" not in json.dumps(typer.plan)


def _find(node, key):
    """Every value under `key` in a plan, depth first."""
    if isinstance(node, dict):
        for k, v in node.items():
            if k == key:
                yield v
            yield from _find(v, key)
    elif isinstance(node, list):
        for v in node:
            yield from _find(v, key)


def test_st6_truncates_before_a_cast_to_an_integer() -> None:
    """ST-6's rewrite, `if x >= 0 then floor(x) else ceil(x)`, then the cast.
    `to_substrait` never asks for it today (#2438): the core's cast reads no
    option."""
    from sverify._substrait_shims import st6

    narrow = {"vt": [*FINITE_A["vt"], _.i >= 0, _.i < 1000]}
    typer, b = _typed(VT.select(c=_.a.cast("int64"), n=_.i.cast("int32")), narrow)
    out = st6(typer, b)
    assert out == {"shim": "casts to integers: if x >= 0 then floor(x) else ceil(x), then the cast"}
    text = json.dumps(typer.plan)
    assert "floor" in text and "ceil" in text and "gte" in text
    # Only the double's cast: the integer's is exact already.
    assert len(list(_find(typer.plan, "ifThen"))) == 1
    typer2, b2 = _typed(VT.select(n=_.i.cast("int32")), narrow)
    assert st6(typer2, b2) is None


def test_st8_holds_or_refuses_by_the_decimal_calls() -> None:
    """ST-8 rewrites nothing: it holds when every decimal call is a `+`, `-` or
    `*` whose result keeps every digit, and refuses any other decimal call."""
    from sverify._substrait_shims import st8

    d = ibis.table({"d": "decimal(10,2)", "e": "decimal(12,3)"}, name="d")
    typer, b = _typed(d.select(s=_.d + _.e, p=_.d * _.e, m=_.e - _.d))
    assert st8(typer, b) == {
        "shim": "none needed: no decimal operation of the plan reduces its scale",
        "rewrite": False,
    }
    typer, b = _typed(d.select(a=_.d.abs()))
    assert any(c.name == "abs" for c in typer.calls)
    assert st8(typer, b) is None


# -- ST-6: a cast of a double to an integer (#2438) ------------------------------------

F = ibis.table({"a": "float64"}, name="f")
CAST = F.select(c=_.a.cast("int64"))
#: #2438's repro: no NULL, no NaN, a bound that keeps the cast inside 64 bits.
F_BOUNDED = {"f": [_.a.notnull(), ~_.a.isnan(), _.a >= -100.0, _.a <= 100.0]}
#: Values where truncation, ties away from zero and ties to even disagree, with
#: the integers truncation gives.
TRUNCATED = [(2.5, 2), (-2.5, -2), (-0.5, 0), (3.5, 3), (-3.7, -3)]


@functools.cache
def _cast_report() -> sv.Report:
    """#2438's report, verified once for the export tests."""
    return _verify(CAST, F_BOUNDED)


def _casts(node) -> list[dict]:
    """The `cast` expressions of a Substrait plan in JSON form."""
    if isinstance(node, dict):
        here = [node["cast"]] if isinstance(node.get("cast"), dict) else []
        return here + [c for v in node.values() for c in _casts(v)]
    if isinstance(node, list):
        return [c for v in node for c in _casts(v)]
    return []


def test_st6_apply_truncates_before_the_cast() -> None:
    """#2438: the cast reads `float_to_int`, which Substrait leaves open (ST-6),
    so `apply` writes the truncation before it."""
    exported = read(_cast_report().to_substrait(shims="apply"))
    [shim] = [s for s in exported.manifest["shims"] if s["option"] == "float_to_int"]
    assert shim["gap"] == "ST-6"
    assert not exported.manifest["assumptions"]
    [cast] = _casts(exported.plan)
    assert "ifThen" in cast["input"], cast


def test_st6_shim_is_exact_under_every_rounding() -> None:
    """The cast's input is integral after the shim, so a consumer's cast gives the
    reference's truncation whichever way it rounds (`float_to_int`'s three modes)."""
    plan = read(_cast_report().to_substrait(shims="apply")).plan
    [cast] = _casts(plan)
    modes = {
        "TRUNCATE": math.trunc,
        "TIE_AWAY_FROM_ZERO": lambda v: math.copysign(math.floor(abs(v) + 0.5), v),
        "TIE_TO_EVEN": round,
    }
    for x, want in TRUNCATED:
        y = _evaluate(plan, cast["input"], (x,))
        assert {name: int(r(y)) for name, r in modes.items()} == dict.fromkeys(modes, want), x


def test_st6_annotate_ships_the_assumption() -> None:
    m = read(_cast_report().to_substrait(shims="annotate")).manifest
    [found] = [a for a in m["assumptions"] if a["option"] == "float_to_int"]
    assert (found["gap"], found["assumes"]) == ("ST-6", ["TRUNCATE"])
    assert not [s for s in m["shims"] if s["option"] == "float_to_int"]


def test_st6_refuse_names_the_gap() -> None:
    with pytest.raises(ExportError, match=re.escape("(ST-6, upstream/bugs/ST-6.json)")):
        _cast_report().to_substrait(shims="refuse")


def test_st6_apply_plan_truncates_on_duckdb() -> None:
    """The plan `apply` writes, read back and run on DuckDB, whose own cast rounds
    half to even (duckdb-R9), gives the reference's truncation."""
    pytest.importorskip("duckdb")
    report = _verify(CAST, F_BOUNDED)
    back = sv.Report.from_substrait(report.to_substrait(shims="apply"))
    con = connect()
    put_table(con, "f", pa.table({"a": pa.array([x for x, _ in TRUNCATED], pa.float64())}))
    for r in (report, back):
        assert r.run(con, "duckdb").column("c").to_pylist() == [y for _, y in TRUNCATED]


def test_st6_shim_passes_nan_and_infinities_to_the_cast() -> None:
    """NaN and the infinities pass through the shim (`ceil(NaN)` is NaN) and reach the
    cast, which throws (`failureBehavior`), as DuckDB's cast of NaN does."""
    duckdb = pytest.importorskip("duckdb")
    plan = read(_cast_report().to_substrait(shims="apply")).plan
    [cast] = _casts(plan)
    assert cast["failureBehavior"] == "FAILURE_BEHAVIOR_THROW_EXCEPTION"
    for x in (NAN, float("inf"), float("-inf")):
        y = _evaluate(plan, cast["input"], (x,))
        assert y != y if x != x else y == x
        with pytest.raises(duckdb.Error):
            duckdb.execute("SELECT CAST(?::DOUBLE AS BIGINT)", [y]).fetchall()


# -- #2439: MIN and MAX read `list_null_order` of lists only ------------------------------

MM = ibis.table({"i": "int64", "x": "float64", "s": "string"}, name="mm")


def _reads_list_null_order(report: sv.Report) -> bool:
    return any(d["option"] == "list_null_order" for d in report._depends or [])


@pytest.mark.parametrize("col", ["i", "x", "s"])
@pytest.mark.parametrize("fn", ["min", "max"])
def test_min_and_max_of_a_value_that_is_no_list_depend_on_no_list_order(fn: str, col: str) -> None:
    """#2439: `list_null_order` was met by every `MIN` and `MAX`, whatever the
    argument's type; its scope is a list argument (`optionScope`, whose `#guard`s
    in `Scopes.lean` cover a list's, since the model refuses `MIN` of a list)."""
    assert not _reads_list_null_order(_verify(MM.aggregate(m=getattr(MM[col], fn)())))


@pytest.mark.parametrize("col", ["i", "x"])
@pytest.mark.parametrize("fn", ["min", "max"])
def test_min_and_max_of_numbers_export(fn: str, col: str) -> None:
    """The default export refused every `MIN` and `MAX` at `list_null_order` (#2439)."""
    m = read(_verify(MM.aggregate(m=getattr(MM[col], fn)())).to_substrait()).manifest
    rows = [r for k in ("shims", "assumptions", "unexercised", "up_to") for r in m[k]]
    assert not [r for r in rows if r.get("option") == "list_null_order"], m


def test_max_of_strings_has_no_substrait_impl() -> None:
    """Substrait's YAMLs have no `min` or `max` of strings: the export refuses for that
    reason alone, after #2439."""
    with pytest.raises(ExportError, match=r"no impl of max in Substrait's YAMLs takes \(string\)"):
        _verify(MM.aggregate(m=MM.s.max())).to_substrait()
