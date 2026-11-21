"""`sverify check query.sql --schema FILE` (#1362): a bare SQL file as a target, its exit
codes and the same JSON and SARIF documents as for a Python file."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from sverify.cli import main

SCHEMA = "orders:\n  id: BIGINT NOT NULL\n  amount: INTEGER\n"


def _run(capsys, *argv: str) -> tuple[int, str]:
    code = main(list(argv))
    return code, capsys.readouterr().out


def _files(tmp_path: Path, sql: str, schema: str = SCHEMA, name: str = "schema.yaml"):
    q = tmp_path / "model.sql"
    q.write_text(sql)
    s = tmp_path / name
    s.write_text(schema)
    return str(q), str(s)


def test_a_proved_query_exits_0(tmp_path, capsys) -> None:
    q, s = _files(tmp_path, "SELECT id, amount FROM orders WHERE amount > 10;")
    code, out = _run(capsys, "check", q, "--schema", s)
    assert code == 0 and "proved" in out


def test_a_query_that_can_raise_exits_1_naming_the_precondition(tmp_path, capsys) -> None:
    q, s = _files(tmp_path, "SELECT id, amount * 2 AS d FROM orders")
    code, out = _run(capsys, "check", q, "--schema", s)
    assert code == 1 and "overflow" in out


def test_json_schema_file_and_the_json_document(tmp_path, capsys) -> None:
    q, s = _files(
        tmp_path,
        "SELECT id FROM orders",
        '{"orders": {"id": "BIGINT NOT NULL"}}',
        "schema.json",
    )
    code, out = _run(capsys, "check", q, "--schema", s, "--format", "json")
    doc = json.loads(out)
    assert code == 0 and doc["command"] == "check" and doc["exit"] == 0
    (item,) = doc["items"]
    assert item["name"] == "model" and item["status"] == "proved"
    assert "report" in item


def test_the_sarif_document(tmp_path, capsys) -> None:
    q, s = _files(tmp_path, "SELECT id, amount * 2 AS d FROM orders")
    code, out = _run(capsys, "check", q, "--schema", s, "--format", "sarif")
    assert code == 1 and json.loads(out)["version"] == "2.1.0"


@pytest.mark.parametrize(
    ("sql", "text"),
    [
        ("SELECT id FROM orders; SELECT 1", "one query per file"),
        ("", "one query per file"),
        ("SELECT id FROM orders PIVOT x", "cannot parse"),
        ("SELECT id FROM nowhere", "no schema for: nowhere"),
    ],
)
def test_a_file_that_is_not_one_query_over_the_schema_is_a_usage_error(
    tmp_path, capsys, sql: str, text: str
) -> None:
    q, s = _files(tmp_path, sql)
    code, out = _run(capsys, "check", q, "--schema", s)
    assert code == 2 and text in out


def test_a_missing_schema_flag_or_file_is_a_usage_error(tmp_path, capsys) -> None:
    q, s = _files(tmp_path, "SELECT id FROM orders")
    assert _run(capsys, "check", q)[0] == 2
    assert _run(capsys, "check", q, "--schema", str(tmp_path / "none.yaml"))[0] == 2
    (tmp_path / "bad.yaml").write_text("orders: [id]")
    assert _run(capsys, "check", q, "--schema", str(tmp_path / "bad.yaml"))[0] == 2


def test_an_outside_the_subset_construct_exits_3_by_name(tmp_path, capsys) -> None:
    q, s = _files(tmp_path, "SELECT id, amount::DOUBLE::BIGINT AS a FROM orders")
    code, out = _run(capsys, "check", q, "--schema", s)
    assert code == 3 and "unsupported" in out


def test_dialect_and_semantics_are_svs(tmp_path, capsys) -> None:
    q, s = _files(tmp_path, "SELECT id FROM orders")
    assert _run(capsys, "check", q, "--schema", s, "--dialect", "duckdb")[0] == 0
    assert _run(capsys, "check", q, "--schema", s, "--semantics", "duckdb")[0] == 0
    assert _run(capsys, "check", q, "--schema", s, "--dialect", "snowflake")[0] == 2


def test_the_sql_flags_are_refused_for_a_python_file(tmp_path, capsys) -> None:
    py = tmp_path / "p.py"
    py.write_text("x = 1\n")
    assert _run(capsys, "check", str(py), "--schema", "s.yaml")[0] == 2
    q, s = _files(tmp_path, "SELECT id FROM orders")
    assert _run(capsys, "check", q, "--schema", s, "--fix")[0] == 2
