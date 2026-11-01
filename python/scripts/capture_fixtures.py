"""Capture real Substrait plans from DataFusion into tests/fixtures/df_*.json,
and from Isthmus into tests/fixtures/isthmus_*.json.

The pipelines are the Ibis expressions in `sverify_dev.examples`, compiled to SQL by
Ibis and to Substrait by DataFusion, the same route incremental maintenance takes.
The Isthmus plans are SQL that pins down what the parser reads (and refuses)
of Calcite's encodings; they are captured only where an Isthmus binary is
found (`$SVERIFY_ISTHMUS`, or `isthmus` on `PATH`).

Run from python/:  uv run python scripts/capture_fixtures.py
"""

import json
from pathlib import Path

import ibis

from sverify.asof import asof_join
from sverify.engine import (
    _isthmus,
    connect,
    create_table,
    isthmus_json,
    isthmus_path,
    substrait_json,
    to_sql,
)
from sverify_dev.examples import PIPELINES, UNSUPPORTED, create_tables, customers, orders

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
    # Sorts, DISTINCT, semi, anti and outer joins.
    "order_by": orders.order_by([ibis.desc("amount"), "customer"]),
    "order_by_limit": orders.order_by("amount").limit(2, offset=1),
    "distinct": orders.select("customer", "amount").distinct(),
    "semi_join": orders.semi_join(customers, orders.customer == customers.name),
    "anti_join": orders.anti_join(customers, orders.customer == customers.name),
    "outer_join": orders.outer_join(customers, orders.customer == customers.name),
    # The string functions of `SubstraitLean/Text.lean` (regular expressions,
    # which Lean does not evaluate, are in `tests/test_backends.py`).
    "strings": customers.select(
        upper=customers.name.upper(),
        lower=customers.city.lower(),
        length=customers.name.length(),
        sub=customers.name.substr(1, 2),
        find=customers.name.find("b"),
        like=customers.city.like("R%"),
        strip=customers.city.strip(),
        concat=customers.name + "@" + customers.city,
        starts=customers.name.startswith("a"),
        ends=customers.city.endswith("e"),
    ),
    # The time functions of `SubstraitLean/Time.lean`.
    "time": SENSORS.select(
        "ts",
        year=SENSORS.ts.year(),
        quarter=SENSORS.ts.quarter(),
        month=SENSORS.ts.month(),
        week=SENSORS.ts.week_of_year(),
        day=SENSORS.ts.day(),
        dow=SENSORS.ts.day_of_week.index(),
        doy=SENSORS.ts.day_of_year(),
        hour=SENSORS.ts.hour(),
        to_second=SENSORS.ts.truncate("s"),
        to_minute=SENSORS.ts.truncate("m"),
        to_day=SENSORS.ts.truncate("D"),
        to_week=SENSORS.ts.truncate("W"),
        to_quarter=SENSORS.ts.truncate("Q"),
        to_year=SENSORS.ts.truncate("Y"),
    ),
    # Not in the modelled fragment: recorded to pin down the rejection.
    "aggregate": UNSUPPORTED["aggregate"],
}


EVENTS = ibis.table(
    {
        "d": "date",
        "d2": "date",
        "ts": "timestamp",
        "x": "int64",
        "s": "string",
        "ok": "boolean",
        "v": "float64",
    },
    name="events",
)

ISTHMUS = {
    # `add:date_iday` adds days and microseconds: refused (#17).
    "date_iday": "SELECT d, d + INTERVAL '1' DAY AS next_day, d < d + INTERVAL '7' DAY AS later "
    "FROM events",
    # `lt:date_date`, `gt:date_date`: dates compare as days.
    "date_compare": "SELECT d FROM events WHERE d < d2 AND d > DATE '2024-01-01'",
    # VARCHAR literals (CASE), CHAR literals (cast for `||`) and a timestamp
    # literal at precision 0.
    "char_literals": "SELECT CASE WHEN x > 1 THEN 'big' ELSE 'small' END AS size, s || 'z' AS sz "
    "FROM events WHERE ts > TIMESTAMP '2024-01-01 00:00:00'",
    # `'ab '` is CHAR(3) with a trailing blank: refused.
    "char_padding": "SELECT CHAR_LENGTH('ab ') AS n FROM events",
    # Window functions inside expressions are hoisted into `Rel.window`.
    "nested_window": "SELECT x, ROW_NUMBER() OVER (PARTITION BY s ORDER BY x) - 1 AS rn0, "
    "x - LAG(x) OVER (PARTITION BY s ORDER BY x) AS dx, "
    "ROW_NUMBER() OVER (PARTITION BY s ORDER BY x) AS rn FROM events",
    "is_true": "SELECT ok IS TRUE AS t, ok IS NOT FALSE AS nf FROM events WHERE (x > 3) IS TRUE",
    # `power:i64_i64` returns a double: its integer arguments are converted.
    "power": "SELECT POWER(x, 2) AS p FROM events",
    # Calcite's AVG of integers is an integer (`avg:i64`): refused.
    "avg_integer": "SELECT s, AVG(x) AS a FROM events GROUP BY s",
    # An integer compared with a double is cast to a double.
    "compare_int_double": "SELECT x FROM events WHERE x > v",
}

#: Captured with DDL of its own: a TIMESTAMP(0) column (seconds), refused.
ISTHMUS_SECONDS = (
    'CREATE TABLE "secs" ("ts" TIMESTAMP)',
    "SELECT ts FROM secs WHERE ts > TIMESTAMP '2024-01-01 00:00:00'",
)


def capture_isthmus() -> None:
    binary = isthmus_path()
    if binary is None:
        print("no Isthmus binary: skipping tests/fixtures/isthmus_*.json")
        return
    con = connect(sql_producer="isthmus")
    create_table(con, "events", EVENTS.schema())
    plans = {name: isthmus_json(con, sql) for name, sql in ISTHMUS.items()}
    plans["timestamp_seconds"] = _isthmus(binary, ISTHMUS_SECONDS[:1], ISTHMUS_SECONDS[1])
    for name, plan in plans.items():
        path = FIXTURES / f"isthmus_{name}.json"
        path.write_text(json.dumps(json.loads(plan), indent=2) + "\n")
        print(f"wrote {path.relative_to(FIXTURES.parents[1])}")


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
    capture_isthmus()


if __name__ == "__main__":
    main()
