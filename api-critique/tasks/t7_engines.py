"""Task 7: run one job on DuckDB and on Polars, and understand the difference.

Integer division, string functions, a window with a key, a sort with LIMIT;
each run on both engines by route="auto", then semantics="polars".
"""

import datetime as dt

import ibis
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.errors import RouteError

con = sv.connect()
con.put(
    "events",
    pa.table(
        {
            "id": pa.array([1, 2, 3, 4], pa.int64()),
            "user": ["Ada", "bob", "Cy", "bob"],
            "ms": pa.array([-7, 5, 12, 9], pa.int64()),
            "ts": [dt.datetime(2026, 1, 1, h) for h in (1, 2, 3, 4)],
        }
    ),
)
e = con.table("events")
REQ = {
    "events": [
        sv.unique("id"),
        _.id.notnull(),
        _.ms.between(-1000, 1000),
        _.user.notnull(),
        _.ts.notnull(),
        _.ts.between(dt.datetime(2000, 1, 1), dt.datetime(2100, 1, 1)),
    ]
}

jobs = {
    "int division": e.select(e.id, secs=e.ms // 1000, rem=e.ms % 1000),
    "strings": e.select(e.id, u=e.user.lower(), n=e.user.length(), p=e.user.substr(0, 2)),
    "window by key": e.mutate(prev=e.ms.lag().over(ibis.window(group_by=e.user, order_by=e.id))),
    "top 2": e.order_by(ibis.desc(e.ms)).limit(2),
    "hourly": e.group_by(h=e.ts.truncate("h")).aggregate(n=e.count(), s=e.ms.sum()),
    "mean": e.group_by("user").aggregate(m=e.ms.mean()),
}

for name, expr in jobs.items():
    rep = sv.verify(expr, requires=REQ)
    line = f"{name:14} proved={rep.proved!s:5}"
    for engine in ("duckdb", "polars"):
        try:
            out = rep.run(con, engine)
            line += f" | {engine}: {rep.routes[engine].kind}/{rep.routes[engine].cls} {out.num_rows} rows"
        except RouteError as err:
            line += f" | {engine}: RouteError {str(err)[:200]}"
        except Exception as err:
            line += f" | {engine}: {type(err).__name__} {str(err)[:200]}"
    print(line)

# Results equal? Compare one by hand, then with the report's observation.
rep = sv.verify(jobs["int division"], requires=REQ)
a, b = rep.run(con, "duckdb"), rep.run(con, "polars")
print("\nint division, duckdb:", a.to_pylist()[:1], "polars:", b.to_pylist()[:1])
print("observation.equal:", rep.observation.equal(a, b))

# semantics="polars": what changes?
rp = sv.verify(jobs["int division"], requires=REQ, semantics="polars")
print("\nsemantics=polars proved:", rp.proved)
print("polars:", rp.run(con, "polars").to_pylist()[:1], rp.routes["polars"])
try:
    rp.run(con, "duckdb")
except RouteError as err:
    print("duckdb:", err)

# Which engines did each report consider? Is there a one-call matrix?
print("\nroutes attr:", type(rep.routes), list(rep.routes))
print("Route fields:", [f for f in dir(rep.routes["polars"]) if not f.startswith("_")])
