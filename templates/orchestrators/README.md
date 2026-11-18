# Orchestrator examples

One transform, `big_orders` in `orders.py`, verified three ways:

- In CI: `sverify check templates/orchestrators/orders.py`. The decorator declares the input
  schema (`schemas=`), so the check proves the contract without a driver script.
- In Dagster: `dagster_asset.py` has an asset that applies the transform and a blocking asset
  check that proves the contract before the run.
- In Airflow: `airflow_dag.py` has a task that proves the contract and fails the run when it
  is not proved, followed by a task that applies the transform.

`python/tests/test_orchestrator_templates.py` runs each example; the Dagster and Airflow tests
skip when the orchestrator is not installed. These are examples to copy, not maintained
integrations. Tested versions are in [compatibility](../pipelines/docs/compatibility.md).
