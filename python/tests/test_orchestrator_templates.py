"""The orchestrator examples in `templates/orchestrators/` run: the contract
is proved, the transform applies to data, and a failing proof fails the
orchestrator's step (#1485, #787)."""

from __future__ import annotations

import importlib.util
import sys

import pytest

import sverify as sv
from _repo import ROOT, needs_repo

pytestmark = needs_repo

TEMPLATES = ROOT / "templates" / "orchestrators"


def _load(name: str):
    sys.path.insert(0, str(TEMPLATES))
    try:
        spec = importlib.util.spec_from_file_location(f"_tpl_{name}", TEMPLATES / f"{name}.py")
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module
    finally:
        sys.path.remove(str(TEMPLATES))
        sys.modules.pop("orders", None)


def test_the_contract_is_proved_and_applies() -> None:
    orders = _load("orders")
    assert orders.prove().verdict == sv.Verdict.PROVED
    import pyarrow as pa

    out = orders.run(pa.table({"id": [1, 2, 3], "amount": [5, 20, 50]}))
    assert out["amount"].to_pylist() == [20, 50]


def test_the_file_is_checked_by_the_cli(capsys: pytest.CaptureFixture[str]) -> None:
    from sverify.cli import main

    assert main(["check", str(TEMPLATES / "orders.py")]) == 0


def test_dagster_asset_and_check() -> None:
    dg = pytest.importorskip("dagster")
    module = _load("dagster_asset")
    result = dg.materialize([module.big_orders], instance=dg.DagsterInstance.ephemeral())
    assert result.success
    check = module.big_orders_contract()
    assert check.passed


def test_airflow_dag_proves_then_runs() -> None:
    pytest.importorskip("airflow")
    module = _load("airflow_dag")
    dag = module.dag_object
    assert [t.task_id for t in dag.topological_sort()] == ["prove", "run"]
    assert dag.get_task("prove").python_callable() == "proved"
    assert dag.get_task("run").python_callable() == 2
