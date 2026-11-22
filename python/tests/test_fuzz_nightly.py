"""The nightly fuzz run's ledger (`sverify_dev.fuzz_nightly`), without running
a fuzzer."""

import json

import pytest

from _repo import needs_repo

nightly = pytest.importorskip("sverify_dev.fuzz_nightly")


def test_shape_blanks_literals_and_spacing():
    assert nightly.shape("SELECT  1.5, 'a''b'\n FROM t WHERE i > 42") == (
        "SELECT ?, ? FROM t WHERE i > ?"
    )


@pytest.mark.parametrize(
    ("text", "cls"),
    [
        ("DuckDB raises Error('x')", "error"),
        ("Lean: [(nan,)]", "nan"),
        ("[(inf,)]", "inf"),
        ("[(None,)]", "null"),
        ("[(-0.0,)]", "negzero"),
        ("[(1,)] vs [(2,)]", "value"),
    ],
)
def test_value_class(text, cls):
    assert nightly.value_class(text) == cls


def _batch(path, suite, seed, **files):
    path.mkdir()
    meta = {
        "suite": suite,
        "seed": seed,
        "seconds": 60,
        "status": "ok",
        "elapsed": 61,
        "peak_rss_mb": 900,
        "date": "2026-11-19",
    }
    (path / "batch.json").write_text(json.dumps(meta))
    for name, text in files.items():
        target = path / name.replace("__", "/")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    return path


CORE = json.dumps(
    [
        {
            "oracle": "rows:polars",
            "sql": "SELECT i + 1 FROM t",
            "detail": "Lean: [(None,)]",
            "extra": {},
            "seed": 7,
        }
    ]
)
JUNIT = """<testsuites><testsuite><testcase classname="tests.test_floats" name="test_sum[x]">
<failure type="AssertionError" message="assert nan == 0.0"/></testcase>
<testcase classname="tests.test_floats" name="test_ok"/></testsuite></testsuites>"""


def test_merge_dedups_by_signature_and_marks_new(tmp_path):
    a = _batch(tmp_path / "a", "core", 7, **{"core.json": CORE})
    # The same mismatch with other literals: one signature.
    b = _batch(tmp_path / "b", "core", 8, **{"core.json": CORE.replace("+ 1", "+ 2")})
    h = _batch(tmp_path / "h", "hypothesis:1/6", 9, **{"junit.xml": JUNIT})
    ledger, night = nightly.merge({}, [a, b, h])
    assert len(ledger["entries"]) == 2
    core = next(e for e in ledger["entries"].values() if e["suite"] == "core")
    assert core["count"] == 2 and core["seeds"] == [7, 8]
    assert core["signature"] == ["core:rows:polars", "SELECT i + ? FROM t", "null"]
    hyp = next(e for e in ledger["entries"].values() if e["suite"] != "core")
    assert hyp["signature"] == [
        "hypothesis:AssertionError",
        "tests/test_floats.py::test_sum",
        "nan",
    ]
    assert "--hypothesis-seed=9" in hyp["repro"]
    assert all(f["new"] for f in night[:1])

    again, night2 = nightly.merge(ledger, [a])
    assert not any(f["new"] for f in night2)
    assert again["entries"][night2[0]["id"]]["count"] == 3


def test_report_lists_stopped_batches_and_new_findings(tmp_path):
    a = _batch(tmp_path / "a", "core", 7, **{"core.json": CORE})
    ledger, night = nightly.merge({}, [a])
    lost = {
        "suite": "duckdb:float_special",
        "seed": 3,
        "status": "memory",
        "elapsed": 40,
        "peak_rss_mb": 7300,
    }
    text = nightly.report(night, [*ledger["last_batches"], lost])
    assert "2 batches (1 stopped), 1 distinct signatures, 1 new, 1 without an explanation" in text
    assert "`duckdb:float_special` seed 3: memory" in text
    assert "## Unexplained" in text and "repro fuzz-ledger.json" in text


def test_repro_writes_a_core_case_and_prints_its_replay(tmp_path, monkeypatch, capsys):
    a = _batch(tmp_path / "a", "core", 7, **{"core.json": CORE})
    ledger, night = nightly.merge({}, [a])
    path = tmp_path / "ledger.json"
    path.write_text(json.dumps(ledger))
    monkeypatch.setattr(nightly.tempfile, "gettempdir", lambda: str(tmp_path))
    nightly.main(["repro", str(path), night[0]["id"]])
    out = capsys.readouterr().out
    assert (
        "sverify_dev.fuzz --replay" in out and (tmp_path / f"fuzz-{night[0]['id']}.json").exists()
    )


@pytest.mark.slow
def test_batch_stops_at_its_wall_time_and_records_it(tmp_path, monkeypatch):
    sleeper = ([nightly.sys.executable, "-c", "import time; time.sleep(60)"], {})
    monkeypatch.setattr(nightly, "command", lambda *a: sleeper)
    rec = nightly.batch("core", 1, 1, tmp_path / "b", timeout=1, rss_mb=10**6)
    assert rec["status"] == "timeout" and rec["elapsed"] < 30
    assert json.loads((tmp_path / "b" / "batch.json").read_text())["status"] == "timeout"


CASE = {
    "sql": "SELECT i + 7 FROM t",
    "query": {
        "sql": "SELECT i + 7 FROM t",
        "out": {},
        "ordered": False,
        "base": None,
        "tlp_pred": None,
    },
    "tables": {"t": [], "u": []},
}


@pytest.mark.slow
def test_a_stopped_batch_records_the_case_it_was_on(tmp_path, monkeypatch):
    # The fuzzer writes each case to $SVERIFY_FUZZ_PROGRESS before checking
    # it; here the "case" hangs and the wall-time limit stops the batch.
    code = (
        "import json, os, time; "
        f"open(os.environ['SVERIFY_FUZZ_PROGRESS'], 'w').write(json.dumps({CASE!r})); "
        "time.sleep(60)"
    )
    monkeypatch.setattr(nightly, "command", lambda *a: ([nightly.sys.executable, "-c", code], {}))
    rec = nightly.batch("core", 4, 1, tmp_path / "b", timeout=3, rss_mb=10**6)
    assert rec["status"] == "timeout"
    ledger, night = nightly.merge({}, [tmp_path / "b"])
    (entry,) = ledger["entries"].values()
    assert entry["signature"] == ["core:timeout", "SELECT i + ? FROM t", "timeout"]
    assert entry["example"]["sql"] == CASE["sql"]
    assert "sverify_dev.fuzz --replay" in entry["repro"]


def test_a_stopped_test_batch_names_each_workers_test(tmp_path):
    d = _batch(tmp_path / "h", "hypothesis:2/6", 5)
    meta = json.loads((d / "batch.json").read_text())
    (d / "batch.json").write_text(json.dumps({**meta, "status": "memory"}))
    (d / "progress.json.gw1").write_text(json.dumps({"node": "tests/test_numeric.py::test_sum"}))
    (found,) = nightly.findings(d)
    assert found["sig"] == ["hypothesis:memory", "tests/test_numeric.py::test_sum", "memory"]
    assert "--hypothesis-seed=5" in found["repro"]


def test_the_checker_over_its_cap_is_a_memory_finding(tmp_path):
    over = json.dumps(
        [
            {
                "oracle": "checker",
                "sql": "SELECT 1",
                "detail": "memory cap: substrait-check used "
                "5000 MB on one request, over its cap of 4096 MB",
                "extra": {"plan": "{}"},
            }
        ]
    )
    duck = json.dumps(
        {
            "results": [
                {
                    "cls": "checker_memory",
                    "sql": "SELECT 2 FROM t",
                    "detail": "memory cap: ...",
                    "plan": "{}",
                }
            ]
        }
    )
    a = _batch(tmp_path / "a", "core", 1, **{"core.json": over})
    b = _batch(tmp_path / "b", "duckdb:float_arith", 2, **{"duckdb__fuzz__float_arith.json": duck})
    ledger, _ = nightly.merge({}, [a, b])
    sigs = sorted(e["signature"] for e in ledger["entries"].values())
    assert sigs == [
        ["core:checker", "SELECT ?", "memory"],
        ["duckdb:float_arith:checker", "SELECT ? FROM t", "memory"],
    ]


def test_a_duckdb_fuzz_disagreement_that_verify_flags_is_no_finding(tmp_path):
    flagged = {
        "cls": "disagree",
        "sql": "SELECT COALESCE(i, (i // i)) FROM t",
        "lean": "error: Substrait.Issue.divByZero",
        "duckdb": "[[0]]",
        "reason": "verify: division by zero: i / i",
    }
    silent = {**flagged, "reason": None, "sql": "SELECT i % -1 FROM t"}
    duck = json.dumps({"results": [flagged, silent]})
    b = _batch(
        tmp_path / "b", "duckdb:int_division", 2, **{"duckdb__fuzz__int_division.json": duck}
    )
    ledger, _ = nightly.merge({}, [b])
    # Only the query `verify` does not flag stays (the rule for `% -1` is tested below).
    [entry] = ledger["entries"].values()
    assert entry["signature"][1] == "SELECT i % -? FROM t"


@needs_repo
def test_the_modulus_rule_explains_a_duckdb_eval_order_mismatch(tmp_path):
    # `i % -1` raises in DuckDB 2.0.0 at MIN (`duckdb-R15-int-modulus`); the
    # reference gives 0. The shipped rule names the fact, whatever the literal.
    mod = {
        "cls": "disagree",
        "sql": "SELECT i % -1 FROM t",
        "lean": "[[0]]",
        "duckdb": "error: Out of Range Error: Overflow in modulus of -9223372036854775808 % -1",
        "reason": None,
    }
    duck = json.dumps({"results": [mod]})
    b = _batch(tmp_path / "b", "duckdb:eval_order", 2, **{"duckdb__fuzz__eval_order.json": duck})
    ledger, night = nightly.merge({}, [b], nightly.load_rules())
    [entry] = ledger["entries"].values()
    assert entry["signature"] == ["duckdb:eval_order", "SELECT i % -? FROM t", "error"]
    assert entry["explained"] == "fact duckdb-R15-int-modulus"
    assert nightly.rule_problems(nightly.load_rules()) == []


@pytest.mark.slow
def test_a_crashed_fuzzer_is_not_ok_and_names_its_last_case(tmp_path, monkeypatch):
    code = (
        "import json, os, sys; "
        f"open(os.environ['SVERIFY_FUZZ_PROGRESS'], 'w').write(json.dumps({CASE!r})); "
        "sys.exit(1)"
    )
    monkeypatch.setattr(nightly, "command", lambda *a: ([nightly.sys.executable, "-c", code], {}))
    # A relative --out, as the workflow passes it: the batch writes there all the same.
    monkeypatch.chdir(tmp_path)
    rec = nightly.batch("core", 4, 1, nightly.Path("out"), timeout=30, rss_mb=10**6)
    assert rec["status"] == "exit 1"
    (found,) = nightly.findings(tmp_path / "out")
    assert found["sig"] == ["core:crash", "SELECT i + ? FROM t", "crash"]


RULES = [
    {"kind": "core:rows:polars", "shape": r"i \+ \?", "class": "null", "issue": 1234},
    {"kind": "hypothesis:AssertionError", "shape": "test_floats", "fact": "DD-1"},
]


def test_a_rule_explains_its_signatures_only(tmp_path):
    a = _batch(tmp_path / "a", "core", 7, **{"core.json": CORE})
    h = _batch(tmp_path / "h", "hypothesis:1/6", 9, **{"junit.xml": JUNIT})
    ledger, night = nightly.merge({}, [a, h], RULES)
    assert sorted(e["explained"] for e in ledger["entries"].values()) == ["#1234", "fact DD-1"]
    # Another value class is another mismatch: the rule doesn't cover it.
    nan = _batch(tmp_path / "n", "core", 8, **{"core.json": CORE.replace("None", "nan")})
    _, night = nightly.merge({}, [nan], RULES)
    assert night[0]["explained"] is None
    text = nightly.report(night, [])
    assert "1 without an explanation" in text and "## Unexplained" in text


def test_a_rule_naming_a_closed_issue_explains_nothing(tmp_path):
    a = _batch(tmp_path / "a", "core", 7, **{"core.json": CORE})
    _, night = nightly.merge({}, [a], RULES)
    text = nightly.report(night, [], closed={1234})
    assert "1 without an explanation" in text and "which is closed" in text
    assert len(nightly.warnings(night, closed={1234})) == 1
    assert nightly.warnings(night) == []


def test_rule_problems_name_bad_rules(tmp_path):
    (tmp_path / "upstream" / "bugs").mkdir(parents=True)
    (tmp_path / "upstream" / "bugs" / "DUCK-1.json").write_text("{}")
    rules = [
        {"kind": "k", "shape": "(", "issue": 1},
        {"kind": "k", "shape": "x", "fact": "nope"},
        {"kind": "k", "shape": "x", "upstream": "DUCK-1"},
        {"kind": "k", "shape": "x", "issue": 1, "fact": "DD-1"},
    ]
    problems = nightly.rule_problems(rules, tmp_path)
    assert [p.split(":")[0] for p in problems] == ["rule 0", "rule 1", "rule 3"]


@needs_repo
def test_the_explanations_file_is_well_formed():
    assert nightly.rule_problems(nightly.load_rules()) == []
