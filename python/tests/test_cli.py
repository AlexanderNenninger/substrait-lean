"""The `sverify` command (#744, API review I1–I5): discovery, exit codes, the
JSON document and its schema, the github and sarif formats,
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
    assert lines[-1] == "paid (p): proved"  # no bare status line after the node's own


def test_a_file_that_is_not_proved_exits_1_with_codes(tmp_path, capsys):
    code, out = run(capsys, "check", str(write(tmp_path, NOT_PROVED)))
    assert code == 1
    assert "  Not proved:" in out
    assert "[may_be_false]" in out
    assert "counterexample:" in out
    assert "NOT proved" in out and out.splitlines()[-1] != "not proved"


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
    assert set(item) == {"name", "nodes", "status", "relaxations", "summary", "links", "report"}
    assert (item["name"], item["nodes"], item["status"]) == ("paid", ["p"], "not_proved")
    assert set(item["summary"]) == {"guarantees", "checks", "not_proved"}
    assert item["report"]["format"] == 4 and item["report"]["proved"] is False


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
    # It says what the fix does to the input (#881 1.4, ruling 219 D4).
    assert "narrow the input each node accepts: its sources must meet them" in out
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


SUM_ONLY = """
@sv.transform(ensures=[_.total > 0])
def per_customer(orders):
    return orders.group_by("customer").agg(total=orders.amount.sum() * 2 + 1)


p = orders.pipe(per_customer)
"""


def test_diff_names_the_other_fixes_where_no_precondition_helps(tmp_path, capsys):
    """An unbounded SUM needs a row cap, not a `requires` the checker infers:
    `--diff` prints the report's hint instead of a dead end (#1485)."""
    path = write(tmp_path, SUM_ONLY)
    code, out = run(capsys, "check", str(path), "--diff")
    assert "No preconditions to add: no proof" not in out
    assert "sv.max_rows(" in out
    assert "$" not in out


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


def test_declared_schemas_let_check_prove_an_unapplied_transform(tmp_path, capsys):
    body = """
    @sv.transform(
        requires=[_.amount >= 0, _.amount < 2**62],
        ensures=[_.amount >= 0],
        schemas={"orders": {"id": "int64", "amount": "int64"}},
    )
    def paid(orders):
        return orders.filter(orders.amount > 10)
    """
    code, doc = run_json(capsys, "check", str(write(tmp_path, body)))
    assert code == 0
    assert doc["unchecked"] == []
    [item] = doc["items"]
    assert (item["name"], item["status"]) == ("paid", "proved")


def test_declared_schemas_report_what_is_not_proved(tmp_path, capsys):
    body = """
    @sv.transform(
        ensures=[_.amount > 10], schemas={"orders": {"id": "int64", "amount": "int64"}}
    )
    def paid(orders):
        return orders.filter(orders.amount > 0)
    """
    code, doc = run_json(capsys, "check", str(write(tmp_path, body)))
    assert code == 1
    [item] = doc["items"]
    assert item["status"] == "not_proved"


def test_schemas_must_name_the_parameters():
    with pytest.raises(TypeError, match="must name each parameter"):

        @sv.transform(schemas={"other": {"id": "int64"}})
        def paid(orders):
            return orders


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
    env = {**os.environ, "SVERIFY_TIMEOUT": "0", "SVERIFY_TEMP_DIRECTORY": str(tmp_path / "spill")}
    argv = [sys.executable, "-m", "sverify.cli", "refresh", f"{path}:stored", "--json"]
    done = subprocess.run(
        [*argv, "--memory-limit", "20MB"], capture_output=True, text=True, env=env
    )
    assert done.returncode == 4, done.stderr
    doc = json.loads(done.stdout)
    assert doc["error"]["code"] == "memory"
    assert doc["error"]["type"] == "MemoryLimitError"
    assert not sink.exists()
    env["SVERIFY_MEMORY_LIMIT"] = "2GB"
    done = subprocess.run(argv, capture_output=True, text=True, env=env)
    assert done.returncode == 0, done.stdout + done.stderr
    assert sink.exists()
    # A breach after an earlier commit leaves that commit as it was (M7).
    from deltalake import DeltaTable

    from sverify.io import DeltaSink

    version, contract = DeltaTable(str(sink)).version(), DeltaSink(str(sink)).contract()
    assert contract is not None
    # A new version of the source, in another file (Python caches the first's
    # bytecode), so the refresh computes again.
    newer = tmp_path / "newer.py"
    newer.write_text(path.read_text().replace('name="orders",', 'name="orders", version=2,'))
    again = [sys.executable, "-m", "sverify.cli", "refresh", f"{newer}:stored", "--json"]
    done = subprocess.run(
        [*again, "--memory-limit", "20MB"], capture_output=True, text=True, env=env
    )
    assert done.returncode == 4, done.stdout + done.stderr
    assert json.loads(done.stdout)["error"]["code"] == "memory"
    after = (DeltaTable(str(sink)).version(), DeltaSink(str(sink)).contract())
    assert after == (version, contract)


def test_a_dbt_project_needs_sverify_dbt(tmp_path, capsys, monkeypatch):
    (tmp_path / "dbt_project.yml").write_text("name: x\n")
    monkeypatch.setattr("shutil.which", lambda _: None)
    code, doc = run_json(capsys, "check", str(tmp_path))
    assert code == 2
    assert "sverify-dbt" in doc["error"]["message"]


def test_a_dbt_project_gets_the_flags_sverify_dbt_parses(tmp_path, capsys, monkeypatch):
    """`sverify check <dbt dir>` hands sverify-dbt the format, the timeout and
    the memory limit, each a flag its parser takes (#891): a rejected flag
    would raise `SystemExit`."""
    sverify_dbt_cli = pytest.importorskip("sverify_dbt.cli")
    (tmp_path / "dbt_project.yml").write_text("name: x\n")
    monkeypatch.setattr("shutil.which", lambda _: "sverify-dbt")
    seen: list[list[str]] = []

    def call(argv: list[str]) -> int:
        seen.append(argv)
        return sverify_dbt_cli.main(argv[1:])

    monkeypatch.setattr("subprocess.call", call)
    for fmt in ("json", "github", "sarif"):
        code, _ = run(capsys, "check", str(tmp_path), "--format", fmt)
        assert code == 2 and seen[-1][-2:] == ["--format", fmt]  # no target/manifest.json
    code, _ = run(capsys, "check", str(tmp_path), "--timeout", "5", "--memory-limit", "1GB")
    assert code == 2
    assert seen[-1][-4:] == ["--timeout", "5", "--memory-limit", "1GB"]


def test_a_source_with_a_schema_is_checked_without_its_table(tmp_path, capsys):
    """`DeltaSource(uri, schema=...)` lets `check` prove a transform over a table
    that does not exist here: no credentials, no network (#1485, 18)."""
    path = tmp_path / "pipeline.py"
    path.write_text(
        textwrap.dedent(
            """\
            import pyarrow as pa
            import sverify as sv
            from ibis import _
            from sverify.io import DeltaSource

            orders = DeltaSource(
                "s3://no-such-bucket/orders",
                schema=pa.schema([("id", pa.int64()), ("amount", pa.int64())]),
            )


            @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount > 10])
            def paid(orders):
                return orders.filter(orders.amount > 10)


            p = orders.pipe(paid)
            """
        )
    )
    code, doc = run_json(capsys, "check", str(path))
    assert code == 0, doc
    [item] = doc["items"]
    assert (item["name"], item["status"]) == ("paid", "proved")


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
    assert s["not_proved"][0].startswith("id is never NULL: it may be")


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
    assert "::amount > 20: it may be FALSE" in line and "%0Acounterexample: " in line


def test_sarif(tmp_path, capsys):
    path = write(tmp_path, NEEDS + NOT_PROVED.replace("paid", "late").replace("p =", "q ="))
    code, out = run(capsys, "check", str(path), "--format", "sarif")
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
    # The first `needs` result carries the fix `check --fix` writes (#793).
    [fix] = results[0]["fixes"]
    assert "fixes" not in results[1] and "fixes" not in results[2]
    [change] = fix["artifactChanges"]
    assert change["artifactLocation"]["uri"] == str(path)
    fixed = path.read_bytes()
    for rep in sorted(change["replacements"], key=lambda r: -r["deletedRegion"]["byteOffset"]):
        at, n = rep["deletedRegion"]["byteOffset"], rep["deletedRegion"]["byteLength"]
        fixed = fixed[:at] + rep["insertedContent"]["text"].encode() + fixed[at + n :]
    assert run(capsys, "check", str(path), "--fix")[0] in (0, 1)
    assert fixed == path.read_bytes()


def test_sarif_is_valid(tmp_path, capsys):
    from _sarif import jsonschema, valid_sarif

    path = write(tmp_path, NEEDS + NOT_PROVED.replace("paid", "late").replace("p =", "q ="))
    code, out = run(capsys, "check", str(path), "--format", "sarif")
    assert code == 1
    assert valid_sarif(out)["runs"][0]["results"]
    with pytest.raises(jsonschema.ValidationError):  # the schema is not vacuous
        valid_sarif('{"version": "2.1.0", "runs": 1}')


def test_help_lists_the_exit_codes(capsys):
    assert main(["--help"]) == 0
    out = capsys.readouterr().out
    assert "  5  a refresh committed with rows quarantined" in out
    assert "  7  refused: no route takes the proved node to the engine" in out
    assert "  8  a refresh held a node" in out


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
    ("policy", "code", "status"), [("quarantine", 5, "quarantined"), ("hold", 8, "held")]
)
def test_refresh_exits_apart_when_rows_are_quarantined_or_held(
    tmp_path, capsys, policy, code, status
):
    path = write(tmp_path, QUARANTINE.replace("POLICY", policy))
    got, doc = run_json(capsys, "refresh", f"{path}:p")
    assert got == code and doc["status"] == status and doc["outcome"] == status
    assert doc["alert"] and "(_.amount >= 20)" in doc["alert"]
    # Rows of the data only with --examples (#887).
    assert "| id |" not in doc["alert"]
    assert all(q["examples"] == [] for n in doc["nodes"] for q in n["quarantine"])
    got, shown = run_json(capsys, "refresh", f"{path}:p", "--examples")
    assert got == code and "| id |" in shown["alert"]
    if policy == "quarantine":
        assert any(q["examples"] for n in shown["nodes"] for q in n["quarantine"])
    got, out = run(capsys, "refresh", f"{path}:p")
    assert got == code and "### paid" in out and "| id |" not in out


def test_a_sql_file_without_schemas_is_a_usage_error_that_names_the_flag(tmp_path, capsys):
    """`sverify check revenue.sql` used to exit 6 with "not a Python file" (#1485); it needs
    `--schema` (#1362)."""
    sql = tmp_path / "revenue.sql"
    sql.write_text("select 1")
    code, out = run(capsys, "check", str(sql))
    assert code == 2
    assert "--schema" in out and "not a Python file" not in out


def test_the_double_cast_is_not_shown_around_an_aggregate(tmp_path, capsys):
    """`amount / DOUBLE(sum(amount))` showed an internal cast (#1485)."""
    src = """
@sv.transform(
    schemas={"orders": {"id": "int64", "amount": "int64"}},
    ensures=[_.share <= 1],
)
def share(orders):
    return orders.select(orders.id, share=orders.amount / orders.amount.sum())
"""
    code, out = run(capsys, "check", str(write(tmp_path, src)))
    assert "DOUBLE(" not in out and "amount / sum(amount)" in out


def test_classifying_an_import_error_in_sverify_errors_does_not_raise(monkeypatch):
    """`sverify.errors` failing to import is the error to classify, not a second
    one raised from the classifier (#1585: a double traceback)."""
    from sverify.cli._main import ERROR, _classify

    monkeypatch.setitem(sys.modules, "sverify.errors", None)  # `import` then raises
    assert _classify(TypeError("boom")) == (ERROR, "error")


CHECKED = NOT_PROVED.replace(
    "ensures=[_.amount > 20])", 'ensures=[_.amount > 20], on_unproved="check")'
)


def test_require_proved_fails_a_node_that_is_only_checked_on_the_data(tmp_path, capsys):
    path = write(tmp_path, HEAD + CHECKED)
    got, doc = run_json(capsys, "check", f"{path}:p")
    assert got == 0 and doc["items"][0]["status"] == "checked"
    assert doc["items"][0]["relaxations"] == ['on_unproved="check"']
    got, doc = run_json(capsys, "check", f"{path}:p", "--require-proved")
    assert got == 1 and doc["status"] == "not_proved"
    assert [f["code"] for f in doc["findings"]] == ["checked_only"]
    got, out = run(capsys, "explain", "checked_only")
    assert got == 0 and "--require-proved" in out


def test_a_proved_node_has_no_relaxations_and_passes_require_proved(tmp_path, capsys):
    path = write(tmp_path, HEAD + PROVED)
    got, doc = run_json(capsys, "check", f"{path}:p", "--require-proved")
    assert got == 0 and doc["items"][0]["relaxations"] == []


def test_the_relaxations_name_each_setting_that_weakens_the_gate(tmp_path, capsys):
    body = PROVED.replace(
        'ensures=[_.amount > 10, sv.unique("id")],',
        'ensures=[_.amount > 10, sv.unique("id")], on_inferred="ignore", check_requires=False,',
    )
    path = write(tmp_path, HEAD + body)
    _, doc = run_json(capsys, "check", f"{path}:p")
    assert doc["items"][0]["relaxations"] == ['on_inferred="ignore"', "check_requires=False"]
