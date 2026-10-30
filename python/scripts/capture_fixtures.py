"""Capture real Substrait plans from DataFusion into tests/fixtures/df_*.json.

The pipelines are the Ibis expressions in `sverify.examples`, compiled to SQL by
Ibis and to Substrait by DataFusion, the same route `IncrementalView` takes.

Run from python/:  uv run python scripts/capture_fixtures.py
"""

import json
from pathlib import Path

import ibis

from sverify.asof import asof_join
from sverify.engine import connect, create_table, substrait_json, to_sql
from sverify.examples import PIPELINES, UNSUPPORTED, create_tables

FIXTURES = Path(__file__).resolve().parents[2] / "tests" / "fixtures"

READINGS = ibis.table({"ts": "timestamp", "value": "float64"}, name="readings")
SENSORS = ibis.table({"sensor": "int64", "ts": "timestamp", "value": "float64"}, name="sensors")
_by_sensor = ibis.window(group_by=SENSORS.sensor, order_by=SENSORS.ts)
ACC = ibis.table({"device": "int64", "ts": "timestamp", "ax": "float64"}, name="acc")
GYR = ibis.table({"device": "int64", "ts": "timestamp", "gx": "float64"}, name="gyr")

CAPTURED = {
    **{k: PIPELINES[k] for k in ["filter_project", "inner_join", "union_all", "self_join"]},
    "float_timestamp": READINGS.filter(
        (READINGS.value != -9999.0) & ~READINGS.value.isnan() & (READINGS.value > 0.5)
    ).select("ts", later=READINGS.ts + ibis.interval(seconds=60), scaled=READINGS.value * 2.5),
    "window": SENSORS.select(
        "sensor",
        "ts",
        prev=SENSORS.value.lag().over(_by_sensor),
        rn=ibis.row_number().over(_by_sensor),
        later=SENSORS.ts.lead(2).over(ibis.window(order_by=ibis.desc(SENSORS.ts))),
    ),
    "asof": asof_join(ACC, GYR, on="ts", by="device", tolerance=ibis.interval(milliseconds=10)),
    # Not in the modelled fragment: recorded to pin down the rejection.
    "aggregate": UNSUPPORTED["aggregate"],
}


def main() -> None:
    con = connect()
    create_tables(con)
    create_table(con, "readings", READINGS.schema())
    create_table(con, "sensors", SENSORS.schema())
    create_table(con, "acc", ACC.schema())
    create_table(con, "gyr", GYR.schema())
    for name, expr in CAPTURED.items():
        plan = json.loads(substrait_json(con, to_sql(expr)))
        path = FIXTURES / f"df_{name}.json"
        path.write_text(json.dumps(plan, indent=2) + "\n")
        print(f"wrote {path.relative_to(FIXTURES.parents[1])}")


if __name__ == "__main__":
    main()
