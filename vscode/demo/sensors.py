"""Sensor alerts (tour notebook 2): three readings above 30 in a row.

Without a key on (device_id, ts), rows may tie in the window's ORDER BY and
the engine picks their order. The quick fix on `unkeyed` adds the key.
"""

import ibis
import sverify as sv
from ibis import _

readings = ibis.table(
    {"device_id": "!int64", "ts": "!timestamp", "temperature": "float64"}, name="readings"
)


def three_high(readings):
    w = ibis.window(group_by="device_id", order_by="ts")
    r = readings.mutate(
        p1=readings.temperature.lag(1).over(w), p2=readings.temperature.lag(2).over(w)
    )
    return r.filter((r.temperature > 30) & (r.p1 > 30) & (r.p2 > 30)).select(
        "device_id", "ts", "temperature"
    )


unkeyed = sv.verify(three_high(readings), ensures=[_.temperature > 30, sv.unique("device_id", "ts")])

keyed = sv.verify(
    three_high(readings),
    requires={"readings": [sv.unique("device_id", "ts")]},
    ensures=[_.temperature > 30, ~_.temperature.isnan(), sv.unique("device_id", "ts")],
)
