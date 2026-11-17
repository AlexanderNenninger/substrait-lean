"""Airflow: a DAG whose first task proves the contract and whose second task
applies the transform.

`prove` fails the run (`AirflowFailException`, no retry) when the contract is
not proved; `run` applies the transform, which checks the preconditions on the
data. CI runs the same proof with `sverify check templates/orchestrators/orders.py`.

Needs `pip install apache-airflow sverify`.
"""

from __future__ import annotations

import orders as contract
import pendulum
import pyarrow as pa
from airflow.sdk import dag, task
from airflow.sdk.exceptions import AirflowFailException


@dag(schedule=None, start_date=pendulum.datetime(2026, 1, 1), catchup=False)
def big_orders():
    @task
    def prove() -> str:
        report = contract.prove()
        if not report.proved:
            raise AirflowFailException(str(report))
        return report.verdict

    @task
    def run() -> int:
        orders = pa.table({"id": [1, 2, 3], "amount": [5, 20, 50]})
        return contract.run(orders).num_rows

    prove() >> run()


dag_object = big_orders()
