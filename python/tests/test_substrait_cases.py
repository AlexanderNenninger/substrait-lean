"""Substrait's own function test cases against `Profile.substrait` (#444,
step 4; `sverify_dev.substrait_cases`).

The reader and the plans are tested on cases written here. The replay runs
every case of `substrait-io/substrait` at the pinned commit (fetched into
`~/.cache/sverify/substrait-tests`) and compares with the ledger
`upstream/substrait-cases.json`: a new disagreement, one the ledger does not
triage, or a ledger that no longer matches the results fails. Without
network, the replay is skipped locally and fails on CI."""

import json
import os
import re
import subprocess
import textwrap
from pathlib import Path

import pytest

from sverify_dev import substrait_cases as sc

ROOT = Path(__file__).resolve().parents[2]


def _cases(tmp_path: Path, text: str, name: str = "arithmetic/x.test") -> list[sc.Case]:
    path = tmp_path / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(text))
    return sc.parse_file(path, tmp_path)


def test_reads_scalar_cases(tmp_path):
    add, err, nested, lam = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_SCALAR_TEST: v1.0
        ### SUBSTRAIT_INCLUDE: extension:io.substrait:functions_arithmetic

        # overflow: comments are groups
        add(120::i8, 10::i8) [overflow:SATURATE, rounding:TIE_TO_EVEN] = 127::i8  # a note
        divide(5::i8, 0::i8) [on_division_by_zero:ERROR] = <!ERROR>
        add(1::i32, add(2::i32, 3::i32)) = add(add(1::i32, 2::i32), 3::i32)
        transform([1, Null]::list<i32?>, (x -> add(x, 2::i32))::func<i32? -> i32?>) = [3]::list<i8>
        """,
    )
    assert (add.kind, add.line, add.area) == ("scalar", 5, "arithmetic")
    assert add.text == "add(120::i8, 10::i8) [overflow:SATURATE, rounding:TIE_TO_EVEN] = 127::i8"
    assert add.options == {"overflow": "SATURATE", "rounding": "TIE_TO_EVEN"}
    assert add.call == sc.Call("add", (sc.Lit("120", sc.Type("i8")), sc.Lit("10", sc.Type("i8"))))
    assert add.expected == sc.Lit("127", sc.Type("i8"))
    assert err.expected == sc.ERROR
    assert isinstance(nested.expected, sc.Call) and isinstance(nested.call.args[1], sc.Call)
    lst, fn = lam.call.args
    assert lst.type == sc.Type("list", False, (sc.Type("i32", True),))
    assert lst.value == ["1", "Null"]
    assert fn == sc.Lambda(
        "x",
        sc.Call("add", (sc.Param("x"), sc.Lit("2", sc.Type("i32")))),
        sc.Type("func", False, (sc.Type("i32", True), sc.Type("i32", True))),
    )


def test_reads_aggregate_and_window_cases(tmp_path):
    col, compact, empty, defined = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_AGGREGATE_TEST: v1.0
        ### SUBSTRAIT_INCLUDE: extension:io.substrait:functions_arithmetic

        sum((1, 2, Null)::i8) = 3::i64?
        ((20, 20), (-3, -3)) corr(col0::fp64, col1::fp64) = 1::fp64?
        (()) std_dev(SAMPLE::enum, col0::fp64) = Null::fp64?
        DEFINE t1(fp64, fp64) = ((20, -20), (-3, 3))
        corr(t1.col0, t1.col1) = -1::fp64?
        """,
    )
    assert col.call.args == (sc.Column(("1", "2", "Null"), sc.Type("i8")),)
    assert compact.table == ((sc.Type("fp64"),) * 2, (("20", "20"), ("-3", "-3")))
    assert empty.table == ((sc.Type("fp64"),), ())
    assert empty.call.args[0] == sc.Enum("SAMPLE")
    assert defined.table == ((sc.Type("fp64"),) * 2, (("20", "-20"), ("-3", "3")))
    assert defined.call.args == (sc.Ref(0), sc.Ref(1))
    (lag,) = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_WINDOW_TEST: v1.0
        DEFINE f1(i32) = ((1998), (1999))
        lag(col0, 1::i32, 5::i32) OVER f1 = (5, 1998)::i32?
        """,
        "window/lag.test",
    )
    assert lag.kind == "window" and lag.table == ((sc.Type("i32"),), (("1998",), ("1999",)))
    assert lag.expected == sc.Column(("5", "1998"), sc.Type("i32", True))


def test_literals():
    ts = sc.literal_body("1999-01-08T01:05:05-08:00", sc.Type("ptstz", False, (6,)))
    assert ts == {"precisionTimestampTz": {"precision": 6, "value": "915786305000000"}}
    assert sc.literal_body("2016-12-31T13:30:15.5", sc.Type("pts", False, (3,))) == {
        "precisionTimestamp": {"precision": 3, "value": "1483191015500"}
    }
    assert sc.literal_body("P1DT2H3M4.45S", sc.Type("iday", False, (2,))) == {
        "intervalDayToSecond": {"days": 1, "seconds": 7384, "subseconds": "45", "precision": 2}
    }
    assert sc.literal_body("P1Y2M", sc.Type("iyear")) == {
        "intervalYearToMonth": {"years": 1, "months": 2}
    }
    assert sc.literal_body("-inf", sc.Type("fp64")) == {"fp64": "-Infinity"}
    assert sc.literal_body("null", sc.Type("i8", True)) == {"null": {"i8": sc.NULLABLE}}
    # A quoted 'null' is text.
    assert sc.literal_body(sc._Quoted("null"), sc.Type("str")) == {"string": "null"}
    with pytest.raises(sc.Refused, match="unsigned"):
        sc.type_json(sc.Type("u!u8"))


def test_runs_cover_the_open_options(tmp_path):
    ext = tmp_path / "ext"
    ext.mkdir()
    (ext / "f.yaml").write_text(
        textwrap.dedent(
            """\
            scalar_functions:
              - name: divide
                impls:
                  - args: [{name: x, value: i8}, {name: y, value: i8}]
                    options:
                      overflow: {values: [SILENT, ERROR]}
                      on_division_by_zero: {values: ["NULL", ERROR]}
                    return: i8
            """
        )
    )
    sc._functions.cache_clear()
    one, bad = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_SCALAR_TEST: v1.0
        divide(6::i8, 3::i8) [overflow:ERROR] = 2::i8
        divide(5::i8, 0::i8) [on_division_by_zero:NAN] = null::i8?
        """,
    )
    assert sc.runs(one, ext) == [
        {"overflow": "ERROR", "on_division_by_zero": "NULL"},
        {"overflow": "ERROR", "on_division_by_zero": "ERROR"},
    ]
    assert sc.stray_options(bad, ext) == ["on_division_by_zero:NAN"]
    result = sc.run_case(bad, ext)
    assert result.cls == "disagree" and result.failing[0].got.startswith("not in the YAML")
    sc._functions.cache_clear()


def test_cases_run_on_the_checker(tmp_path):
    ext = tmp_path / "ext"
    ext.mkdir()
    cases = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_SCALAR_TEST: v1.0
        add(120::i8, 10::i8) [overflow:ERROR] = <!ERROR>
        add(120::i8, 10::i8) [overflow:SATURATE] = 127::i8
        negate(-128::i8) [overflow:SATURATE] = 127::i8
        negate(-128::i8) [overflow:ERROR] = <!ERROR>
        add(1::i8, 1::i8) [overflow:SATURATE] = 3::i8
        cardinality([1, 2, 3]::list<i32>) = 3::i64
        bit_length('abc'::str) = 24::i64
        """,
    )
    got = [sc.run_case(c, ext).cls for c in cases]
    assert got == ["agree"] * 4 + ["disagree", "agree", "refused"]


def test_aggregates_and_windows_run_on_the_checker(tmp_path):
    ext = tmp_path / "ext"
    ext.mkdir()
    cases = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_AGGREGATE_TEST: v1.0
        ((1.0), (3.0), (5.0)) variance(SAMPLE::enum, col0::fp64) = 4.0::fp64?
        ((1.0), (3.0), (5.0)) variance(POPULATION::enum, col0::fp64) = 4.0::fp64?
        max((1, 3, Null)::i64) = 3::i64?
        """,
    )
    assert [sc.run_case(c, ext).cls for c in cases] == ["agree", "disagree", "agree"]
    (lag,) = _cases(
        tmp_path,
        """\
        ### SUBSTRAIT_WINDOW_TEST: v1.0
        DEFINE f1(i32) = ((1998), (1999), (2000))
        lag(col0, 2::i32, 5::i32) OVER f1 = (5, 5, 1998)::i32?
        """,
        "window/lag.test",
    )
    assert sc.run_case(lag, ext).cls == "agree"


def _checkout() -> Path:
    try:
        return sc.fetch()
    except (subprocess.CalledProcessError, OSError) as e:
        if os.environ.get("CI"):
            raise
        pytest.skip(f"no checkout of substrait-io/substrait {sc.TAG}: {e}")


def test_the_ledger_is_current():
    """The replay gives the ledger, and each disagreement is triaged."""
    root = _checkout()
    old = sc.read_ledger()
    results, errors = sc.run_all(root)
    new = sc.ledger(results, errors, old)
    untriaged = [d["case"] for d in new["disagreements"] if d["kind"] not in sc.KINDS]
    assert not untriaged, (
        "new disagreements with Substrait's test cases; triage them in "
        f"upstream/substrait-cases.json ({', '.join(sc.KINDS)}): {untriaged}"
    )
    assert new == old, (
        "upstream/substrait-cases.json is stale: run "
        "`python -m sverify_dev.substrait_cases --write` from python/"
    )


def test_the_triage_names_its_record():
    """A triaged disagreement names an issue (`#n`) or an `ST` entry that
    exists; no line of the cases goes unread."""
    data = sc.read_ledger()
    assert data["unread"] == []
    bugs = ROOT / "upstream" / "bugs"
    for d in data["disagreements"]:
        assert d["kind"] in sc.KINDS, d
        ref = d.get("ref", "")
        assert re.fullmatch(r"#\d+|ST-\d+", ref), d
        if ref.startswith("ST-"):
            doc = json.loads((bugs / f"{ref}.json").read_text())
            assert "upstream/substrait-cases.json" in doc["files"], ref
    totals = data["totals"]
    assert sum(
        t["agree"] + t["refused"] + t["disagree"] for a, t in totals.items() if a != "all"
    ) == (sum(totals["all"].values()))
