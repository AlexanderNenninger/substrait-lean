"""Dagster: an asset, and an asset check that proves its contract.

The asset applies `big_orders` to the orders, which checks the
preconditions on the data. The asset check proves the contract before the
run, from the schema alone, and fails when it is not proved. CI runs the same
proof with `sverify check templates/orchestrators/orders.py`.

Needs `pip install dagster sverify`.
"""

from __future__ import annotations

import dagster as dg
import pyarrow as pa

import orders as contract


@dg.asset
def big_orders() -> pa.Table:
    orders = pa.table({"id": [1, 2, 3], "amount": [5, 20, 50]})
    return contract.run(orders)


@dg.asset_check(asset=big_orders, blocking=True)
def big_orders_contract() -> dg.AssetCheckResult:
    report = contract.prove()
    return dg.AssetCheckResult(
        passed=report.proved,
        metadata={"verdict": report.verdict, "report": dg.MetadataValue.text(str(report))},
    )


defs = dg.Definitions(assets=[big_orders], asset_checks=[big_orders_contract])
