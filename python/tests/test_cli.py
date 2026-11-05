"""The `sverify` command (#744, API review I1–I5): discovery, exit codes, the
JSON document and its schema, the github, sarif and junit formats,
`check --fix`, `refresh`, `explain`, the time budget and DuckDB's memory
limit."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

import sverify as sv
from sverify.cli import discover, main, summary
from sverify.cli._main import split_target

HEAD = """\
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import DeltaSink, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2, 3], "customer": ["a", "b", "a"], "amount": [30, 5, 50]}),
    name="orders",
)
"""

PROVED = """
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1000, sv.unique("id")]},
    ensures=[_.amount > 10, sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount > 10)


p = orders.pipe(paid)
"""

NOT_PROVED = """
@sv.transform(ensures=[_.amount > 20])
def paid(orders):
    return orders.filter(orders.amount > 10)


p = orders.pipe(paid)
"""

NEEDS = """
@sv.transform()
def doubled(orders):
    return orders.select(orders.id, doubled=orders.amount * 2)


d = orders.pipe(doubled)
"""


def write(tmp_path: Path, body: str, name: str = "pipeline.py") -> Path:
    path = tmp_path / name
    path.write_text(HEAD + textwrap.dedent(body))
    return path


def run(capsys, *argv: str) -> tuple[int, str]:
    code = main(list(argv))
    return code, capsys.readouterr().out


SCHEMAS = Path(sv.__file__).resolve().parent / "schemas"


def run_json(capsys, *argv: str) -> tuple[int, dict]:
    """The command's JSON document, checked against the CLI's schema, and
    each embedded report against the report's."""
    code, out = run(capsys, *argv, "--json")
    doc = json.loads(out)
    jsonschema = pytest.importorskip("jsonschema")
    jsonschema.validate(doc, json.loads((SCHEMAS / "cli.schema.json").read_text()))
    report = json.loads((SCHEMAS / "report.schema.json").read_text())
    for item in doc.get("items", []):
        if item["report"] is not None:
            jsonschema.validate(item["report"], report)
    assert doc["exit"] == code
    return code, doc


def test_a_proved_file_exits_0_with_its_contract_in_words(tmp_path, capsys):
    code, out = run(capsys, "check", str(write(tmp_path, PROVED)))
    assert code == 0
    lines = out.splitlines()
    assert lines[0].startswith("Contract of ")
    assert "  The output guarantees:" in lines
    assert "    paid (p): amount > 10; no two rows share id" in lines
    assert "  Each refresh checks on the data:" in lines
    assert any(line.startswith("    paid (p): orders: amount ≥ 0") for line in lines)
    assert "paid (p): proved" in lines
    assert lines[-1] == "proved"


def test_a_file_that_is_not_proved_exits_1_with_codes(tmp_path, capsys):
    code, out = run(capsys, "check", str(write(tmp_path, NOT_PROVED)))
    assert code == 1
    assert "  Not proved:" in out
    assert "[may_be_false]" in out
    assert "counterexample:" in out
    assert out.splitlines()[-1] == "not proved"


def test_the_json_document(tmp_path, capsys):
    path = write(tmp_path, NOT_PROVED)
    code, doc = run_json(capsys, "check", str(path))
    assert code == 1
    assert doc["format"] == 1
    assert doc["command"] == "check"
    assert (doc["exit"], doc["status"]) == (1, "not_proved")
    assert doc["file"] == str(path)
    assert doc["error"] is None
    assert doc["unchecked"] == []
    assert set(doc["budget"]) == {"timeout", "elapsed"}
    [item] = doc["items"]
    assert set(item) == {"name", "nodes", "status", "summary", "links", "report"}
    assert (item["name"], item["nodes"], item["status"]) == ("paid", ["p"], "not_proved")
    assert set(item["summary"]) == {"guarantees", "checks", "not_proved"}
    assert item["report"]["format"] == 2 and item["report"]["proved"] is False


def test_one_node_of_a_file(tmp_path, capsys):
    path = write(tmp_path, PROVED + NOT_PROVED.replace("paid", "late").replace("p =", "q ="))
    code, doc = run_json(capsys, "check", f"{path}:p")
    assert code == 0
    assert [i["nodes"] for i in doc["items"]] == [["p"]]
    code, doc = run_json(capsys, "check", f"{path}:late")
    assert code == 1
    assert [i["name"] for i in doc["items"]] == ["late"]


def test_every_node_is_checked_though_one_fails(tmp_path, capsys):
    """An unproved node does not stop discovery: the ones after it are
    checked too."""
    path = write(tmp_path, NOT_PROVED + PROVED.replace("paid", "ok").replace("p =", "q ="))
    d = discover(path)
    assert d.error is None
    assert [(c.name, c.status) for c in d.checked] == [("paid", "not_proved"), ("ok", "proved")]
    assert d.checked[1].nodes == ["q"]


def test_an_unsupported_construct_exits_3(tmp_path, capsys):
    body = """
    import ibis

    @sv.transform()
    def noisy(orders):
        return orders.select(orders.id, r=ibis.random())


    n = orders.pipe(noisy)
    """
    code, doc = run_json(capsys, "check", str(write(tmp_path, body)))
    assert code == 3
    assert (doc["status"], doc["error"]["code"]) == ("unsupported", "unsupported")
    assert "RandomScalar" in doc["error"]["message"]


def test_needed_preconditions_have_a_code(tmp_path, capsys):
    path = write(tmp_path, NEEDS)
    code, out = run(capsys, "check", str(path))
    assert code == 1
    assert out.count("[needs]") == 2
    code, doc = run_json(capsys, "check", str(path))
    [item] = doc["items"]
    assert {(n["table"], n["column"], n["op"]) for n in item["report"]["needs"]} == {
        ("orders", "amount", ">="),
        ("orders", "amount", "<"),
    }


def test_diff_shows_the_fix_and_fix_writes_it(tmp_path, capsys):
    path = write(tmp_path, NEEDS)
    before = path.read_text()
    code, out = run(capsys, "check", str(path), "--diff")
    assert code == 1
    assert '+@sv.transform(requires={"orders": [' in out
    assert path.read_text() == before
    code, doc = run_json(capsys, "check", str(path), "--fix")
    assert code == 0, doc
    assert doc["applied"] is True
    [fix] = doc["fixes"]
    assert fix["placed"] and set(fix["requires"]) == {"orders"}
    assert '@sv.transform(requires={"orders": [_.amount.isnull() | (_.amount >= -2**62)' in (
        path.read_text()
    )
    code, _ = run(capsys, "check", str(path))
    assert code == 0


@pytest.mark.parametrize(
    "decorator",
    [
        '@sv.transform(requires={"orders": [_.id >= 0]})',
        '@sv.transform(requires={"orders": []})',
        "@sv.transform(requires=[_.id >= 0])",
        '@sv.transform(requires={"other": []} if False else {})',
    ],
)
def test_fix_extends_requires(tmp_path, capsys, decorator):
    path = write(tmp_path, NEEDS.replace("@sv.transform()", decorator))
    code, doc = run_json(capsys, "check", str(path), "--fix")
    [fix] = doc["fixes"]
    if "if False" in decorator:
        assert not fix["placed"] and "not a literal" in fix["reason"]
        assert code == 1
        return
    assert fix["placed"], fix
    assert code == 0, doc
    text = path.read_text()
    assert "_.amount.isnull() | (_.amount < 2**62)" in text
    if "_.id >= 0" in decorator:
        assert "[_.id >= 0, _.amount.isnull()" in text


def test_a_transform_never_applied_is_not_proved(tmp_path, capsys):
    body = """
    @sv.transform(ensures=[_.amount > 10])
    def paid(orders):
        return orders.filter(orders.amount > 10)
    """
    code, doc = run_json(capsys, "check", str(write(tmp_path, body)))
    assert code == 1
    assert doc["unchecked"] == ["paid"]


def test_a_broken_link_is_reported(tmp_path, capsys):
    body = """
    @sv.transform(ensures=[sv.unique("id")])
    def first(orders):
        return orders.distinct(on="id", keep="first") if False else orders


    @sv.transform(requires={"t": [_.amount >= 0]})
    def second(t):
        return t


    s = orders.pipe(first).pipe(second)
    """
    d = discover(write(tmp_path, body))
    second = next(c for c in d.checked if c.name == "second")
    assert second.status == "not_proved"
    assert second.links and "amount" in second.links[0]


def test_usage_errors_exit_2_and_errors_6(tmp_path, capsys):
    code, doc = run_json(capsys, "check", str(tmp_path / "missing.py"))
    assert code == 2 and doc["status"] == "usage"
    path = write(tmp_path, PROVED)
    assert main(["check", str(path), "--no-such-flag"]) == 2
    assert main(["check", str(path), "--fix", "--diff"]) == 2
    assert main(["refresh", f"{path}:p", "--format", "sarif"]) == 2
    capsys.readouterr()
    code, doc = run_json(capsys, "refresh", str(path))
    assert code == 2 and "<file>:<node>" in doc["error"]["message"]
    code, doc = run_json(capsys, "check", f"{path}:nope")
    assert code == 2
    assert "has no node or transform 'nope'" in doc["error"]["message"]
    code, doc = run_json(
        capsys, "check", str(write(tmp_path, "raise RuntimeError('boom')\n", "b.py"))
    )
    assert code == 6 and doc["error"]["message"] == "boom"


def test_a_refresh_at_import_is_refused_while_checking(tmp_path, capsys):
    code, doc = run_json(capsys, "check", str(write(tmp_path, PROVED + "p.refresh()\n")))
    assert code == 6
    assert "__name__" in doc["error"]["message"]


def test_explain_and_the_full_report(tmp_path, capsys):
    code, out = run(capsys, "explain", "may_be_false")
    assert code == 0 and out.startswith("[may_be_false] ")
    code, doc = run_json(capsys, "explain", "may-be-false")  # kebab case reads too
    assert (code, doc["code"], doc["level"]) == (0, "may_be_false", "error")
    code, doc = run_json(capsys, "explain", "no-such-code")
    assert code == 2
    path = write(tmp_path, NOT_PROVED)
    code, out = run(capsys, "check", f"{path}:p", "--full")
    assert code == 1
    assert "  ensures (_.amount > 20): NOT proved" in out


def test_every_code_check_prints_is_explained():
    from typing import get_args

    from sverify.cli import _explain
    from sverify.contracts import UnprovedReason

    reasons = get_args(UnprovedReason)
    assert all(_explain.explain(r) for r in reasons)
    kinds = ["division by zero", "overflow", "cast out of range", "negative exponent"]
    kinds += ["domain error", "SUM overflow", "overflow to infinity"]
    assert all(_explain.explain(k) for k in kinds)


def test_the_time_budget_reports_what_was_proved(tmp_path, capsys):
    body = (
        PROVED
        + """

@sv.transform()
def slow(orders):
    import time

    time.sleep(60)
    return orders


s = orders.pipe(slow)
"""
    )
    code, doc = run_json(capsys, "check", str(write(tmp_path, body)), "--timeout", "3")
    assert code == 4
    assert doc["error"]["code"] == "timeout"
    assert [(i["name"], i["status"]) for i in doc["items"]] == [
        ("paid", "proved"),
        ("slow", "unfinished"),
    ]
    assert doc["items"][1]["report"] is None


def test_the_time_budget_comes_from_the_environment(tmp_path, capsys, monkeypatch):
    path = write(tmp_path, PROVED)
    monkeypatch.setenv("SVERIFY_TIMEOUT", "0.000001")
    code, _ = run(capsys, "check", str(path))
    assert code == 4
    monkeypatch.setenv("SVERIFY_TIMEOUT", "0")  # off
    code, doc = run_json(capsys, "check", str(path))
    assert code == 0 and doc["budget"]["timeout"] == 0


def test_refresh_runs_a_node(tmp_path, capsys):
    sink = tmp_path / "lake" / "paid"
    body = PROVED + f"\nstored = p.write(DeltaSink({str(sink)!r}))\n"
    path = write(tmp_path, body)
    code, doc = run_json(capsys, "refresh", f"{path}:stored")
    assert code == 0, doc
    [node] = doc["nodes"]
    assert node["node"] == "paid"
    assert node["write"]["inserted"] == 2
    code, out = run(capsys, "refresh", f"{path}:stored", "--timeout", "0.000001")
    assert code == 4 and "budget exceeded" in out


def test_refresh_refuses_an_unproved_node(tmp_path, capsys):
    code, doc = run_json(capsys, "refresh", f"{write(tmp_path, NOT_PROVED)}:p")
    assert code == 1
    assert doc["error"]["type"] == "UnverifiedRunError"
    assert doc["error"]["code"] == "not_proved"


MEMORY = """
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import DeltaSink, StaticSource

N = 2_000_000
orders = StaticSource(
    pa.table({"id": pa.array(range(N)), "customer": pa.array([i % 1000 for i in range(N)])}),
    name="orders",
)


@sv.transform()
def ids(orders):
    return orders.group_by("customer").aggregate(n=orders.id.nunique())


stored = orders.pipe(ids).write(DeltaSink(SINK))
"""


def test_a_duckdb_memory_breach_exits_4_and_writes_nothing(tmp_path):
    """In a process of its own: the limit is the process's DuckDB's."""
    sink = tmp_path / "lake" / "ids"
    path = tmp_path / "big.py"
    path.write_text(MEMORY.replace("SINK", repr(str(sink))))
    env = {**os.environ, "SVERIFY_TIMEOUT": "0", "SVERIFY_SPILL_DIRECTORY": str(tmp_path / "spill")}
    argv = [sys.executable, "-m", "sverify.cli", "refresh", f"{path}:stored", "--json"]
    done = subprocess.run(
        [*argv, "--memory-limit", "20MB"], capture_output=True, text=True, env=env
    )
    assert done.returncode == 4, done.stderr
    doc = json.loads(done.stdout)
    assert doc["error"]["code"] == "memory"
    assert not sink.exists()
    env["SVERIFY_MEMORY_LIMIT"] = "2GB"
    done = subprocess.run(argv, capture_output=True, text=True, env=env)
    assert done.returncode == 0, done.stdout + done.stderr
    assert sink.exists()


def test_a_dbt_project_needs_sverify_dbt(tmp_path, capsys, monkeypatch):
    (tmp_path / "dbt_project.yml").write_text("name: x\n")
    monkeypatch.setattr("shutil.which", lambda _: None)
    code, doc = run_json(capsys, "check", str(tmp_path))
    assert code == 2
    assert "sverify-dbt" in doc["error"]["message"]


def test_split_target():
    assert split_target("a/b.py:paid") == (Path("a/b.py"), "paid")
    assert split_target("a/b.py") == (Path("a/b.py"), None)
    assert split_target(r"C:\x\b.py") == (Path(r"C:\x\b.py"), None)
    assert split_target(r"C:\x\b.py:p") == (Path(r"C:\x\b.py"), "p")


def test_summary_of_a_report():
    import ibis

    import sverify as sv

    t = ibis.table({"id": "int64", "amount": "int64"}, name="orders")
    report = sv.verify(
        t.filter(t.amount > 10),
        requires={"orders": [ibis._.amount >= 0, ibis._.amount < 100]},
        ensures=[ibis._.amount > 10, ibis._.id.notnull()],
    )
    s = summary(report)
    assert s["guarantees"] == ["amount > 10"]
    assert s["checks"] == ["orders: amount ≥ 0", "orders: amount < 100"]
    assert s["not_proved"][0].startswith("id is never NULL: not proved")


def test_the_entry_point():
    done = subprocess.run(
        [sys.executable, "-m", "sverify.cli", "--version"], capture_output=True, text=True
    )
    assert done.returncode == 0 and done.stdout.startswith("sverify ")


def test_github_annotations(tmp_path, capsys):
    path = write(tmp_path, NOT_PROVED)
    code, out = run(capsys, "check", str(path), "--format", "github")
    assert code == 1
    [line] = out.splitlines()
    line_no = HEAD.count("\n") + 2  # the decorator, after the blank line
    assert line.startswith(
        f"::error file={path},line={line_no},title=sverify may_be_false%3A paid::"
    )
    assert "ensures (_.amount > 20)" in line and "%0Acounterexample: " in line


def test_sarif(tmp_path, capsys):
    path = write(tmp_path, NEEDS + NOT_PROVED.replace("paid", "late").replace("p =", "q ="))
    code, out = run(capsys, "check", str(path), "--output-format", "sarif")
    assert code == 1
    log = json.loads(out)
    assert log["version"] == "2.1.0"
    [run_] = log["runs"]
    rules = run_["tool"]["driver"]["rules"]
    assert [r["id"] for r in rules] == ["may_be_false", "needs"]
    assert all(r["fullDescription"]["text"] for r in rules)
    results = run_["results"]
    assert [r["ruleId"] for r in results] == ["needs", "needs", "may_be_false"]
    for r in results:
        assert rules[r["ruleIndex"]]["id"] == r["ruleId"]
        assert r["level"] == "error"
        loc = r["locations"][0]["physicalLocation"]
        assert loc["artifactLocation"]["uri"] == str(path) and loc["region"]["startLine"] > 0
    assert "counterexample" in results[2]["properties"]


def test_junit(tmp_path, capsys):
    import xml.etree.ElementTree as ET

    body = PROVED + NOT_PROVED.replace("paid", "late").replace("p =", "q =")
    body += "\n\n@sv.transform()\ndef unused(t):\n    return t\n"
    path = write(tmp_path, body)
    code, out = run(capsys, "check", str(path), "--format", "junit")
    assert code == 1
    root = ET.fromstring(out)
    [suite] = root.findall("testsuite")
    assert (suite.get("tests"), suite.get("failures"), suite.get("skipped")) == ("4", "1", "1")
    cases = {(str(c.get("classname")).rsplit("::", 1)[1], c.get("name")): c for c in suite}
    assert cases[("paid", "ensures (_.amount > 10)")].find("failure") is None
    failure = cases[("late", "(_.amount > 20)")].find("failure")
    assert failure is not None and failure.get("type") == "may_be_false"
    assert "counterexample" in (failure.text or "")
    assert cases[("unused", "unchecked")].find("skipped") is not None


def test_help_lists_the_exit_codes(capsys):
    assert main(["--help"]) == 0
    out = capsys.readouterr().out
    assert "  5  a refresh committed with rows quarantined, or held a node" in out


QUARANTINE = """
@sv.transform(
    requires={"orders": [_.amount >= 20, _.amount < 1000, sv.unique("id")]},
    ensures=[_.amount >= 20, sv.unique("id")],
    on_violation="POLICY",
)
def paid(orders):
    return orders.filter(orders.amount > 10)


p = orders.pipe(paid)
"""


@pytest.mark.parametrize(
    ("policy", "code", "status"), [("quarantine", 5, "quarantined"), ("hold", 5, "held")]
)
def test_refresh_exits_apart_when_rows_are_quarantined_or_held(
    tmp_path, capsys, policy, code, status
):
    path = write(tmp_path, QUARANTINE.replace("POLICY", policy))
    got, doc = run_json(capsys, "refresh", f"{path}:p")
    assert got == code and doc["status"] == status and doc["outcome"] == status
    assert doc["alert"] and "(_.amount >= 20)" in doc["alert"]
    got, out = run(capsys, "refresh", f"{path}:p")
    assert got == code and "### paid" in out
