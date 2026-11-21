# Compatibility

Each cell is tested in CI, checked by hand before a release, or untested
([#787](https://github.com/AlexanderNenninger/substrait-lean/issues/787)). A cell tested in
CI names its test; a cell checked by hand is on the release checklist
(`.claude/skills/release-sverify/SKILL.md`, "Compatibility by hand").

## Stores

| Store | Status | Tested with |
|---|---|---|
| Local disk | tested in CI | [`test_io_sink_readers.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/tests/test_io_sink_readers.py) |
| S3 | tested in CI, against a moto server | [`test_io_delta_s3.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/tests/test_io_delta_s3.py), moto 5.2.5: writes, maintenance and a restart past another writer's compaction |
| MinIO | checked by hand | MinIO with the open-source Unity Catalog, before a release |
| R2, GCS, Azure | untested | |

## Catalogs

| Catalog | Status | Tested with |
|---|---|---|
| Delta tables by path | tested in CI | [`test_io_sink_readers.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/tests/test_io_sink_readers.py), deltalake 1.6.6 |
| Unity Catalog, open source (`uc://`) | tested in CI against a stand-in for delta-rs's catalog, and checked by hand with MinIO, before a release | [`test_io_delta_catalog.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/tests/test_io_delta_catalog.py) |
| Databricks Unity Catalog, AWS Glue, S3 Tables, Snowflake Open Catalog | checked by hand | the release checklist |
| Iceberg SQL catalog (SQLite) | tested in CI | [`test_io_iceberg.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/tests/test_io_iceberg.py), pyiceberg 0.12.0 |
| Iceberg REST catalogs (Lakekeeper, Polaris), Nessie, Hive Metastore | untested | |

The S3, GCS and Azure rows, and the Unity Catalog, REST and Nessie rows, move to tested in CI when
the containers of [#787](https://github.com/AlexanderNenninger/substrait-lean/issues/787) run.

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
