"""`check` on compiled dbt projects: the sample project and small ones."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
import sverify
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
    assert all(t.status == "not checked" for t in result["org_depth"].tests)


def test_a_surrogate_key_is_never_null(result: sverify_dbt.CheckResult) -> None:
    """md5 is lifted (#725): the key is never NULL, and not shown unique,
    since md5 is not injective."""
    assert statuses(result["stg_order_items"]) == {
        "not_null(item_key)": "proved",
        "unique(item_key)": "not proved",
    }


def test_revenue_of_non_negative_products_is_non_negative(
    result: sverify_dbt.CheckResult,
) -> None:
    """Rounding keeps the sign (#441): `sum(qty * price)` is at least 0."""
    got = statuses(result["customer_revenue_by_category"])
    assert got == {"dbt_utils.accepted_range(books)": "proved"}


def test_the_suggested_source_test_proves_arr(result: sverify_dbt.CheckResult) -> None:
    """`mrr`'s max_value came from `sverify-dbt suggest` (PROOF-STATUS.md)."""
    m = result["subscription_arr"]
    assert m.needed == []
    assert statuses(m) == {"dbt_utils.accepted_range(arr)": "proved"}
    assert result.suggestions() == []


def test_contracts(result: sverify_dbt.CheckResult) -> None:
    m = result["customer_revenue_by_category"]
    assert m.contract == []
    assert [(c.label, c.status) for c in m.constraints] == [("primary_key(customer_id)", "proved")]
    assert result["stg_orders"].contract is None


def test_report_text(result: sverify_dbt.CheckResult) -> None:
    text = str(result)
    assert "proved before the model runs" in text
    assert "refused: sverify cannot read WITH RECURSIVE yet" in text
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
    assert values == {t.name for t in result.proved_tests}
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
    assert set(res.result) == {t.name for t in result.proved_tests}
    dbt(shop, "compile")  # the selectors file parses


def test_the_readmes_sample_is_what_check_prints(shop: Path) -> None:
    """Each model's block in the README's sample output is a block of what
    `check` prints on `examples/shop` (#891, 1.7)."""
    readme = (Path(__file__).parents[1] / "README.md").read_text()
    start = readme.index("On the sample project in")
    sample = readme[readme.index("```\n", start) + 4 :].split("\n```")[0]
    printed = str(sverify_dbt.check(shop, counterexamples=0)).split("\n\n")
    for block in sample.split("\n\n"):
        assert block.strip() in [b.strip() for b in printed], block


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
    # `sverify check <dbt dir> --format json` forwards `--format` (#891).
    assert main(["check", str(shop), "--format", "json", "--counterexamples", "0"]) == 0
    assert json.loads(capsys.readouterr().out) == data
    assert main(["check", str(shop), "--format", "text", "--counterexamples", "0"]) == 0
    assert "stg_orders (models/staging/stg_orders.sql)" in capsys.readouterr().out
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
      - name: ledger
        columns:
          - {name: kind, data_type: varchar}
          - {name: amount, data_type: "decimal(10,2)"}
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


def test_an_ephemeral_model_is_inlined_into_its_reader(make_project) -> None:
    """dbt inlines an ephemeral model into each reader as a CTE: the reader
    reads the ephemeral's inputs, which `check` finds two hops up (#891)."""
    root = make_project(
        {
            "models/_sources.yml": SOURCES,
            "models/stg.sql": (
                "{{ config(materialized='ephemeral') }}\n"
                "select id, cents from {{ source('raw', 'payments') }}\n"
            ),
            "models/totals.sql": (
                "select id, sum(cents) as cents from {{ ref('stg') }} group by id\n"
            ),
            "models/_models.yml": """\
            version: 2
            models:
              - name: totals
                columns:
                  - {name: id, data_tests: [unique]}
              - name: stg
                columns:
                  - {name: id, data_tests: [not_null]}
            """,
        }
    )
    res = sverify_dbt.check(root, counterexamples=0)
    assert res["totals"].refused is None, res["totals"].refused
    # A test on the ephemeral model is listed, not checked: dbt runs none on it.
    assert statuses(res["stg"]) == {"not_null(id)": "not checked"}
    assert statuses(res["totals"]) == {"unique(id)": "proved"}
    assert res["stg"].refused is None
    assert any("inlines it into totals" in n for n in res["stg"].notes)


def test_a_decimal_sum_notes_the_type_sverify_and_duckdb_differ_on(make_project) -> None:
    """`Report.output` types a decimal `SUM` as the reference does, `DECIMAL(p + 10, s)`;
    dbt's own SQL builds DuckDB's `DECIMAL(38, s)`; the contract check keeps DuckDB's (#1484)."""
    root = make_project(
        {
            "models/_sources.yml": SOURCES,
            "models/sums.sql": (
                "select kind, sum(amount) as amount\n"
                "from {{ source('raw', 'ledger') }} group by kind\n"
            ),
            "models/_models.yml": """\
            version: 2
            models:
              - name: sums
                config: {contract: {enforced: true}}
                columns:
                  - {name: kind, data_type: varchar}
                  - {name: amount, data_type: "decimal(38,2)"}
        """,
        }
    )
    sums = sverify_dbt.check(root, counterexamples=0)["sums"]
    assert sums.contract == []
    assert any(
        "column amount: sverify's plan has type DECIMAL(20,2), and DuckDB's SQL gives DECIMAL(38,2)"
        in n
        for n in sums.notes
    )


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


def _incremental(make_project, config: str):
    return sverify_dbt.check(
        make_project(
            {
                "models/_sources.yml": SOURCES,
                "models/p.sql": (
                    "{{ config(materialized='incremental'" + config + ") }}\n"
                    "select id, cents from {{ source('raw', 'payments') }}\n"
                    "{% if is_incremental() %}\n"
                    "where id > (select max(id) from {{ this }})\n"
                    "{% endif %}\n"
                ),
                "models/_models.yml": """\
                version: 2
                models:
                  - name: p
                    columns:
                      - name: id
                        data_tests: [unique, not_null]
            """,
            }
        ),
        counterexamples=0,
    )


@pytest.mark.parametrize(
    ("config", "skippable"),
    [
        (", incremental_strategy='append'", False),
        (", unique_key='id', incremental_strategy='append'", False),
        (", unique_key='id'", False),
        (", unique_key='id', incremental_strategy='merge'", True),
        (", unique_key='id', incremental_strategy='delete+insert'", True),
        (", unique_key='cents', incremental_strategy='merge'", False),
    ],
)
def test_an_incremental_models_tests_are_skippable_only_if_its_key_holds(
    make_project, config: str, skippable: bool
) -> None:
    """An incremental run writes rows the full refresh's proof does not
    cover: with `append`, or `merge` on another key, `dbt build` keeps the
    tests, which are still proved for the full refresh."""
    res = _incremental(make_project, config)
    assert statuses(res["p"]) == {"unique(id)": "proved", "not_null(id)": "proved"}
    assert [t.skippable for t in res["p"].tests] == [skippable, skippable]
    names = {t.name for t in res.proved_tests}
    selected = {n["value"] for n in res.selector()["definition"].get("union", [])}
    assert (selected == names) if skippable else not (selected & names)
    assert ("dbt build may skip them" in str(res)) == skippable
    if not skippable:
        assert "proved for the full refresh (dbt build still runs them)" in str(res)


def test_a_merge_keeps_only_the_key_and_row_level_tests_skippable(make_project) -> None:
    """`unique(cents)` holds for the batch and the full refresh, but a merge on
    `id` can leave an old row and a batch row with the same `cents`: old
    `(1, 5)`, batch `(2, 5)`. It stays out of the skippable set; `unique(id)`
    and the row-level `not_null(id)` stay in."""
    res = sverify_dbt.check(
        make_project(
            {
                "models/_sources.yml": SOURCES.replace(
                    "{name: cents, data_type: integer}",
                    "{name: cents, data_type: integer, data_tests: [unique]}",
                ),
                "models/p.sql": (
                    "{{ config(materialized='incremental', unique_key='id', "
                    "incremental_strategy='merge') }}\n"
                    "select id, cents from {{ source('raw', 'payments') }}\n"
                ),
                "models/_models.yml": """\
                version: 2
                models:
                  - name: p
                    columns:
                      - name: id
                        data_tests: [unique, not_null]
                      - name: cents
                        data_tests: [unique]
            """,
            }
        ),
        counterexamples=0,
    )
    assert {t.label: t.skippable for t in res["p"].tests} == {
        "unique(id)": True,
        "not_null(id)": True,
        "unique(cents)": False,
    }


def test_not_a_duckdb_project(tmp_path: Path) -> None:
    (tmp_path / "target").mkdir()
    (tmp_path / "target" / "manifest.json").write_text(
        json.dumps({"metadata": {"adapter_type": "snowflake"}, "nodes": {}, "sources": {}})
    )
    with pytest.raises(sverify_dbt.ProjectError, match="DuckDB projects only"):
        sverify_dbt.check(tmp_path)
    with pytest.raises(sverify_dbt.ProjectError, match="dbt compile"):
        sverify_dbt.check(tmp_path / "nowhere")


def test_needs_become_suggested_source_tests(make_project, capsys) -> None:
    root = make_project(
        {
            "models/_sources.yml": """\
            version: 2
            sources:
              - name: raw
                schema: main
                tables:
                  - name: subs
                    columns:
                      - name: mrr
                        data_type: bigint
                        data_tests:
                          - not_null
        """,
            "models/arr.sql": "select mrr * 12 as arr from {{ source('raw', 'subs') }}\n",
            "models/_models.yml": """\
            version: 2
            models:
              - name: arr
                columns:
                  - name: arr
                    data_tests: [not_null]
        """,
        }
    )
    res = sverify_dbt.check(root, counterexamples=0)
    m = res["arr"]
    assert [(n.on, n.column) for n in m.needed] == [
        ("source('raw', 'subs')", "mrr"),
        ("source('raw', 'subs')", "mrr"),
    ]
    assert "mrr * 12" in (m.needed[0].because or "")
    assert statuses(m) == {"not_null(arr)": "not proved"}
    # `arr` is never NULL by the source's own test; the model may still overflow (#701).
    assert (m.tests[0].why or "").startswith("it holds, but the model may fail")
    assert "on source('raw', 'subs'), column mrr: dbt_utils.accepted_range" in str(res)
    [a, b] = res.suggestions()
    assert (a.relation.name, a.column) == ("subs", "mrr")
    text = res.suggestions_yaml()
    data = yaml.safe_load(text)
    [source] = data["sources"]
    [table] = source["tables"]
    [col] = table["columns"]
    assert (source["name"], table["name"], col["name"]) == ("raw", "subs", "mrr")
    ranges = [t["dbt_utils.accepted_range"]["arguments"] for t in col["data_tests"]]
    assert {k for r in ranges for k in r} == {"min_value", "max_value", "inclusive"}
    assert "# arr: overflow in `mrr * 12` otherwise" in text
    assert main(["suggest", str(root)]) == 0
    assert capsys.readouterr().out == text


def test_a_seed_takes_its_types_from_the_catalog_of_the_loaded_table(make_project):
    """The dbt default: a seed states no types. Once `dbt seed` has loaded it,
    `dbt docs generate` records the table's real types; before, the refusal
    says what to run (#1586). The CSV is not sniffed: DuckDB reads `1` as
    BIGINT where dbt-duckdb loads INTEGER."""
    from conftest import dbt

    root = make_project(
        {
            "seeds/raw_orders.csv": "id,cents\n1,100\n2,250\n",
            "models/stg.sql": "select id, cents from {{ ref('raw_orders') }}\n",
        }
    )
    why = sverify_dbt.check(root, counterexamples=0)["stg"].refused
    assert why is not None
    assert why.startswith("ref('raw_orders') has no column types") and "`dbt seed`" in why
    dbt(root, "seed")
    dbt(root, "docs", "generate")
    assert sverify_dbt.check(root, counterexamples=0)["stg"].refused is None


def test_a_missing_column_type_message_parses(make_project):
    res = sverify_dbt.check(
        make_project(
            {
                "models/_sources.yml": (
                    "version: 2\nsources:\n  - name: raw\n    schema: main\n"
                    "    tables:\n      - name: payments\n"
                ),
                "models/p.sql": "select 1 as id from {{ source('raw', 'payments') }}\n",
            }
        ),
        counterexamples=0,
    )
    why = res["p"].refused
    assert why is not None and why.startswith("source('raw', 'payments') has no column types")


def test_an_incremental_model_compiled_after_its_run_asks_for_full_refresh(make_project):
    """After `dbt run`, a plain compile renders the `{{ this }}` branch (#1586)."""
    from conftest import dbt

    root = make_project(
        {
            "seeds/raw.csv": "id\n1\n2\n",
            "models/p.sql": (
                "{{ config(materialized='incremental') }}\n"
                "select id from {{ ref('raw') }}\n"
                "{% if is_incremental() %}\n"
                "where id > (select max(id) from {{ this }})\n"
                "{% endif %}\n"
            ),
        }
    )
    dbt(root, "seed")
    dbt(root, "run")
    dbt(root, "docs", "generate")
    dbt(root, "compile")
    why = sverify_dbt.check(root, counterexamples=0)["p"].refused
    assert why and "dbt compile --full-refresh" in why and "{{ this }}" in why
    dbt(root, "compile", "--full-refresh")
    assert sverify_dbt.check(root, counterexamples=0)["p"].refused is None


def test_selectors_need_a_check_of_the_whole_project(shop: Path, tmp_path: Path) -> None:
    """A selector written from `--select` would drop every other model's proved
    tests, so `dbt build` would run them again (#891, 1.6)."""
    partial = sverify_dbt.check(shop, select=["stg_orders"], counterexamples=0)
    with pytest.raises(ValueError, match="whole project"):
        partial.write_selectors(tmp_path / "selectors.yml")
    with pytest.raises(SystemExit) as e:
        main(["check", str(shop), "--select", "stg_orders", "--selectors"])
    assert e.value.code == 2
    full = sverify_dbt.check(shop, counterexamples=0)
    assert full.write_selectors(tmp_path / "selectors.yml").is_file()


def test_an_unreadable_condition_is_dropped_and_the_rest_proved() -> None:
    """#699: `verify` names the condition it cannot read; sverify-dbt drops it
    and proves the others, in one retry per bad condition (no dbt needed)."""
    from types import SimpleNamespace
    from typing import Any, cast

    from sverify_dbt.check import _Checker
    from sverify_dbt.result import ModelResult, TestResult

    bad, good = TestResult(None, None, "bad", "test"), TestResult(None, None, "good", "test")
    res = ModelResult("m", "model.p.m", None, "m")
    res.sql = "SELECT x FROM t"
    ensures = [(bad, ["zz > 1"]), (good, ["x IS NOT NULL"])]
    report = _Checker._verify(
        cast(
            Any,
            SimpleNamespace(counterexamples=0, _drop=_Checker._drop, _isolate=_Checker._isolate),
        ),
        res,
        {"t": {"x": "BIGINT NOT NULL"}},
        {},
        ensures,
    )
    assert bad.status == "not checked" and "cannot read" in (bad.why or "")
    assert good.status == "pending" and report is not None
    assert [r.condition for r in report.ensures] == ["x IS NOT NULL"]


def test_a_refusal_after_planning_is_isolated_to_its_test() -> None:
    """A refusal `ConditionError` does not name (the checker's) skips only the
    test whose conditions fail; the others are proved."""
    from sverify_dbt.check import _Checker
    from sverify_dbt.result import ModelResult, TestResult

    bad, good = TestResult(None, None, "bad", "test"), TestResult(None, None, "good", "test")
    res = ModelResult("m", "model.p.m", None, "m")

    def go(req: dict, ens: list) -> str:
        if "boom" in ens:
            raise ValueError("the checker refuses boom")
        return "report"

    out = _Checker._isolate(go, res, {"t": []}, [(bad, ["boom"]), (good, ["ok"])], ValueError("x"))
    assert out == "report" and bad.status == "not checked" and good.status == "pending"


def test_a_manifest_of_another_schema_version_warns(tmp_path: Path) -> None:
    """sverify-dbt reads manifest v12; an older one reads, with a warning (#891, 1.8)."""
    import json

    from sverify_dbt.manifest import ProjectError, load

    (tmp_path / "target").mkdir()
    meta = {"dbt_schema_version": "https://schemas.getdbt.com/dbt/manifest/v11.json"}
    (tmp_path / "target" / "manifest.json").write_text(json.dumps({"metadata": meta}))
    with pytest.warns(UserWarning, match="schema v12.*v11"), pytest.raises(ProjectError):
        load(tmp_path)  # the adapter check follows


def test_sverify_dbt_and_sverify_are_one_version() -> None:
    assert sverify_dbt.__version__ == sverify.__version__


def test_a_sverify_of_another_version_stops_the_import(monkeypatch: pytest.MonkeyPatch) -> None:
    import importlib
    import importlib.metadata

    real = importlib.metadata.version
    monkeypatch.setattr(
        importlib.metadata, "version", lambda n: "0.0.1" if n == "sverify-dbt" else real(n)
    )
    with pytest.raises(ImportError, match="needs sverify"):
        importlib.reload(sverify_dbt)
    monkeypatch.undo()
    importlib.reload(sverify_dbt)


def test_suggest_names_the_source_test_for_a_null_that_comes_through_an_expression(
    make_project,
) -> None:
    """`fct.not_null(order_day)` fails on `ordered_at = NULL`; sverify itself
    suggests nothing, so sverify-dbt tries `not_null` on the inputs (#1994)."""
    root = make_project(
        {
            "models/_sources.yml": """\
            version: 2
            sources:
              - name: raw
                schema: main
                tables:
                  - name: orders
                    columns:
                      - {name: id, data_type: bigint, data_tests: [not_null]}
                      - {name: ordered_at, data_type: timestamp}
                      - {name: note, data_type: varchar}
        """,
            "models/fct.sql": (
                "select id, cast(ordered_at as date) as order_day, note\n"
                "from {{ source('raw', 'orders') }}\n"
            ),
            "models/_models.yml": """\
            version: 2
            models:
              - name: fct
                columns:
                  - name: order_day
                    data_tests: [not_null]
        """,
        }
    )
    res = sverify_dbt.check(root, counterexamples=0)
    assert statuses(res["fct"]) == {"not_null(order_day)": "not proved"}
    [s] = res.suggestions()
    assert (s.relation.name, s.column, s.test) == ("orders", "ordered_at", "not_null")
    assert "fct: proves not_null(order_day)" in s.because
