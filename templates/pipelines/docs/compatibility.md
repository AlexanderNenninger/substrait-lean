# Compatibility

Each cell is tested in CI, checked by hand before a release, or untested
([#787](https://github.com/AlexanderNenninger/substrait-lean/issues/787)). This page holds the
orchestrator cells so far; stores and catalogs follow with the `compat` job.

## Orchestrators

| Orchestrator | Example | Status | Tested with |
|---|---|---|---|
| GitHub Actions | `check.yml`, `refresh.yml` of this template | used by the template's own CI | GitHub-hosted runners |
| Dagster | [`dagster_asset.py`](../../orchestrators/dagster_asset.py): an asset and a blocking asset check | tested in `tests/test_orchestrator_templates.py` | dagster 1.13.30 |
| Airflow | [`airflow_dag.py`](../../orchestrators/airflow_dag.py): a task that proves, then a task that runs | tested in `tests/test_orchestrator_templates.py` | apache-airflow 3.4.0 |
| Prefect, Kubernetes CronJob, GitLab CI | none yet | untested | |

The two tests skip when the orchestrator is not installed, so a plain test run does not exercise
them. Run them with `uv run --with dagster --with apache-airflow pytest tests/test_orchestrator_templates.py`
from `python/`; the versions above are the ones that run installed.
