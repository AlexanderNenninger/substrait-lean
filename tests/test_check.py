"""`check` on compiled dbt projects: the sample project and small ones."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml

import sverify_dbt
from sverify_dbt.cli import main


@pytest.fixture(scope="module")
def result(shop: Path) -> sverify_dbt.CheckResult:
    return sverify_dbt.check(shop, counterexamples=50)


def statuses(m: sverify_dbt.ModelResult) -> dict[str, str]:
    return {t.label: t.status for t in m.tests}


def test_staging_tests_are_proved_from_source_tests(result: sverify_dbt.CheckResult) -> None:
    got = statuses(result["stg_orders"])
    for label in [
        "not_null(order_id)",
        "unique(order_id)",
        "not_null(customer_id)",
        "dbt_utils.accepted_range(amount)",
    ]:
        assert got[label] == "proved", label


def test_window_test_is_proved(result: sverify_dbt.CheckResult) -> None:
    got = statuses(result["customer_history"])
    assert got["dbt_utils.expression_is_true(valid_to > valid_from)"] == "proved"
    assert got["dbt_utils.unique_combination_of_columns(customer_id, valid_from)"] == "proved"


def test_unproved_key(result: sverify_dbt.CheckResult) -> None:
    [t] = [t for t in result["orders_with_city"].tests if t.label == "unique(order_id)"]
    assert t.status == "not proved"
    assert t.why == "the tests upstream do not make it a key"


def test_refused_models_say_why(result: sverify_dbt.CheckResult) -> None:
    assert "WITH RECURSIVE" in (result["org_depth"].refused or "")
    assert "MD5" in (result["stg_order_items"].refused or "")
    assert all(t.status == "not checked" for t in result["org_depth"].tests)


def test_needed_becomes_a_source_test(result: sverify_dbt.CheckResult) -> None:
    m = result["subscription_arr"]
    [n] = m.needed
    assert (n.on, n.column) == ("source('app', 'subscriptions')", "mrr")
    assert n.test.startswith("dbt_utils.accepted_range: {arguments: {max_value: ")
    assert "mrr * 12" in (n.because or "")
    [t] = m.tests
    assert t.status == "not proved" and "needs" in (t.why or "")


def test_contracts(result: sverify_dbt.CheckResult) -> None:
    m = result["customer_revenue_by_category"]
    assert m.contract == []
    assert [(c.label, c.status) for c in m.constraints] == [("primary_key(customer_id)", "proved")]
    assert result["stg_orders"].contract is None


def test_report_text(result: sverify_dbt.CheckResult) -> None:
    text = str(result)
    assert "proved before the model runs" in text
    assert "refused: sverify cannot read WITH RECURSIVE yet" in text
    assert "on source('app', 'subscriptions'), column mrr: dbt_utils.accepted_range" in text
    assert text.endswith(result.summary())
    json.dumps(result.to_dict())


def test_selectors_keep_other_selectors(result: sverify_dbt.CheckResult, tmp_path: Path) -> None:
    path = tmp_path / "selectors.yml"
    path.write_text(
        yaml.safe_dump(
            {
                "selectors": [
                    {"name": "mine", "definition": {"method": "tag", "value": "x"}},
                    {"name": "sverify_proved", "definition": {"method": "fqn", "value": "old"}},
                ]
            }
        )
    )
    result.write_selectors(path)
    data = yaml.safe_load(path.read_text())
    assert [s["name"] for s in data["selectors"]] == ["mine", "sverify_proved"]
    values = {d["value"] for d in data["selectors"][1]["definition"]["union"]}
    assert values == {t.name for t in result.proved}
    assert "not_null_stg_orders_order_id" in values


def test_dbt_excludes_the_proved_tests(shop: Path, result: sverify_dbt.CheckResult) -> None:
    from conftest import dbt

    result.write_selectors(shop / "selectors.yml")
    runner = pytest.importorskip("dbt.cli.main").dbtRunner()
    res = runner.invoke(
        [
            "ls",
            "--project-dir",
            str(shop),
            "--profiles-dir",
            str(shop),
            "--resource-type",
            "test",
            "--select",
            "selector:sverify_proved",
            "--output",
            "name",
            "--quiet",
        ]
    )
    assert res.success
    assert set(res.result) == {t.name for t in result.proved}
    dbt(shop, "compile")  # the selectors file parses


def test_cli(shop: Path, capsys: pytest.CaptureFixture[str]) -> None:
    assert main(["check", str(shop), "--select", "stg_orders", "--counterexamples", "0"]) == 0
    out = capsys.readouterr().out
    assert out.startswith("stg_orders (models/staging/stg_orders.sql)")
    assert "customer_history" not in out
    assert (
        main(["check", str(shop), "--fail-on", "unproved", "--json", "--counterexamples", "0"]) == 1
    )
    data = json.loads(capsys.readouterr().out)
    assert {m["name"] for m in data["models"]} >= {"stg_orders", "org_depth"}
    assert main(["check", str(shop / "nowhere")]) == 2


SOURCES = """\
version: 2
sources:
  - name: raw
    schema: main
    tables:
      - name: payments
        columns:
          - {name: id, data_type: bigint, data_tests: [not_null, unique]}
          - {name: cents, data_type: integer}
          - name: kind
            data_type: varchar
            data_tests:
              - accepted_values: {arguments: {values: [card, cash]}}
      - name: untyped
"""


def test_contract_mismatch_and_inputs_without_types(make_project) -> None:
    root = make_project(
        {
            "models/_sources.yml": SOURCES,
            "models/totals.sql": (
                "select kind, sum(cents) as cents, count(*) as n\n"
                "from {{ source('raw', 'payments') }} group by kind\n"
            ),
            "models/latest.sql": "select * from {{ source('raw', 'untyped') }}\n",
            "models/downstream.sql": "select id from {{ ref('latest') }}\n",
            "models/_models.yml": """\
            version: 2
            models:
              - name: totals
                config: {contract: {enforced: true}}
                columns:
                  - name: kind
                    data_type: varchar
                    constraints: [{type: not_null}]
                    data_tests: [unique]
                  - {name: cents, data_type: bigint}
                  - {name: n, data_type: bigint}
                  - {name: extra, data_type: date}
        """,
        }
    )
    res = sverify_dbt.check(root, counterexamples=20)
    totals = res["totals"]
    problems = {i.column: i.problem for i in totals.contract or []}
    assert problems["cents"] == "declared bigint, but DuckDB gives HUGEINT"
    assert problems["extra"] == "declared, but the model has no such column"
    assert statuses(totals) == {"unique(kind)": "proved"}
    [nn] = totals.constraints
    assert nn.status == "not proved" and nn.counterexample
    assert "no column types" in (res["latest"].refused or "")
    assert "no column types" in (res["downstream"].refused or "")
    assert main(["check", str(root), "--counterexamples", "0"]) == 1


def test_model_tests_are_inputs_downstream(make_project) -> None:
    """A test on a model is a precondition of the models that read it, when
    it blocks `dbt build`; a warning is not. Only tests carry over: `b`
    knows `a.id` is a key because `a` tests it."""
    root = make_project(
        {
            "models/_sources.yml": SOURCES,
            "models/a.sql": "select id, cents from {{ source('raw', 'payments') }}\n",
            "models/b.sql": "select id, cents from {{ ref('a') }} where cents is not null\n",
            "models/_models.yml": """\
            version: 2
            models:
              - name: a
                columns:
                  - name: id
                    data_tests: [unique, not_null]
                  - name: cents
                    data_tests:
                      - not_null:
                          config: {severity: warn}
              - name: b
                columns:
                  - name: id
                    data_tests: [unique, not_null]
                  - name: cents
                    data_tests: [not_null]
        """,
        }
    )
    res = sverify_dbt.check(root, counterexamples=0)
    assert statuses(res["a"]) == {
        "unique(id)": "proved",
        "not_null(id)": "proved",
        "not_null(cents)": "not proved",
    }
    assert statuses(res["b"]) == {
        "unique(id)": "proved",
        "not_null(id)": "proved",
        "not_null(cents)": "proved",
    }
    assert any("severity warn" in s for s in res["b"].not_assumed)


def test_not_a_duckdb_project(tmp_path: Path) -> None:
    (tmp_path / "target").mkdir()
    (tmp_path / "target" / "manifest.json").write_text(
        json.dumps({"metadata": {"adapter_type": "snowflake"}, "nodes": {}, "sources": {}})
    )
    with pytest.raises(sverify_dbt.ProjectError, match="DuckDB projects only"):
        sverify_dbt.check(tmp_path)
    with pytest.raises(sverify_dbt.ProjectError, match="dbt compile"):
        sverify_dbt.check(tmp_path / "nowhere")
