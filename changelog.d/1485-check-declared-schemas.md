### `sverify check` proves a decorated transform on its declared schemas

`@sv.transform(schemas={"orders": {"id": "int64", "amount": "int64"}})` gives a
transform its input schemas. `sverify check pipeline.py` then proves the contract
of a transform the file never applies, as `paid.check(orders=...)` does, with no
driver script. Without `schemas` the file's `unchecked` message names the new
exit (#1485, item 10).

### Dagster and Airflow examples

`templates/orchestrators/` has a Dagster asset check and an Airflow DAG that prove a
transform's contract before they run it, tested with dagster 1.13.30 and
apache-airflow 3.4.0 ([compatibility](templates/pipelines/docs/compatibility.md), #787).
