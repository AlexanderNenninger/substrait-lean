"""Dagster: an asset, and an asset check that proves its contract.

The asset applies `big_orders` to the orders, which checks the
preconditions on the data. The asset check proves the contract before the
run, from the schema alone, and fails when it is not proved. CI runs the same
proof with `sverify check templates/orchestrators/orders.py`.

Needs `pip install dagster sverify`.
"""

from __future__ import annotations

import dagster as dg
import orders as contract
import pyarrow as pa

import sverify as sv


@dg.asset
def big_orders() -> pa.Table:
    orders = pa.table({"id": [1, 2, 3], "amount": [5, 20, 50]})
    return contract.run(orders)


@dg.asset_check(asset=big_orders, blocking=True)
def big_orders_contract() -> dg.AssetCheckResult:
    report = contract.prove()
    return dg.AssetCheckResult(
        passed=report.verdict != sv.Verdict.UNPROVED,
        metadata={"verdict": report.verdict.value, "report": dg.MetadataValue.text(str(report))},
    )


defs = dg.Definitions(assets=[big_orders], asset_checks=[big_orders_contract])
