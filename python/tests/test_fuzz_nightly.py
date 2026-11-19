"""The nightly fuzz run's ledger (`sverify_dev.fuzz_nightly`), without running
a fuzzer."""

import json

import pytest

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
    assert "2 batches (1 stopped), 1 distinct signatures, 1 new." in text
    assert "`duckdb:float_special` seed 3: memory" in text
    assert "## New" in text and "repro fuzz-ledger.json" in text


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
