"""Task 5: requires/ensures on doubles, with tolerances.

A data scientist's feature table: per-sensor mean, stddev and a z-score
bound; then run on DuckDB and Polars and compare.
"""

import pyarrow as pa
from ibis import _

import sverify as sv

con = sv.connect()
con.put(
    "readings",
    pa.table({"sensor": ["a", "a", "a", "b", "b"], "temp_c": [20.1, 20.4, 19.9, -3.0, -2.5]}),
)
r = con.table("readings")
features = r.group_by("sensor").aggregate(
    mean_t=r.temp_c.mean(), sd_t=r.temp_c.std(), lo=r.temp_c.min(), hi=r.temp_c.max(), n=r.count()
)

# Attempt 1: what I know about the physics, no tolerance.
rep = sv.verify(
    features,
    requires={"readings": [_.temp_c.between(-90, 60), _.sensor.notnull()]},
    ensures=[_.mean_t >= -90, _.mean_t <= 60, _.sd_t >= 0, _.lo <= _.mean_t, _.mean_t <= _.hi],
)
print("attempt 1 proved:", rep.proved)
print(rep)

# Attempt 2: the report suggested sv.approx / a row cap; add both.
rep2 = sv.verify(
    features,
    requires={"readings": [_.temp_c.between(-90, 60), _.sensor.notnull(), sv.max_rows(10_000_000)]},
    ensures=[
        sv.approx(_.mean_t >= -90),
        sv.approx(_.mean_t <= 60),
        (_.sd_t >= 0) | _.sd_t.isnull(),
        # sv.approx(_.lo <= _.mean_t) raised TypeError: approx takes column-vs-number only
        sv.equivalent(floats=sv.within(abs=1e-9)),
    ],
)
print("\nattempt 2 proved:", rep2.proved)
print(rep2)
print("epsilon:", rep2.epsilon)

# Attempt 3: a tolerance at least the proved bound, relative this time.
for tol in [sv.within(rel=1e-9), sv.within(abs=1e-3), sv.within(ulps=4)]:
    rep3 = sv.verify(
        features,
        requires={"readings": [_.temp_c.between(-90, 60), _.sensor.notnull(), sv.max_rows(10_000_000)]},
        ensures=[sv.approx(_.mean_t <= 60), sv.equivalent(floats=tol)],
    )
    print(f"\nattempt 3 {tol}: proved={rep3.proved}")
    try:
        a = rep3.run(con, "duckdb")
        b = rep3.run(con, "polars")
        print("  routes:", {k: str(v) for k, v in rep3.routes.items()})
        print("  equal under observation:", rep3.observation.equal(a, b))
    except Exception as e:
        print(f"  {type(e).__name__}: {str(e)[:500]}")

# Attempt 4: drop MIN/MAX (refused on Polars), compare engines; then no observation at all.
feat2 = r.group_by("sensor").aggregate(mean_t=r.temp_c.mean(), n=r.count())
for ens in ([sv.equivalent(floats=sv.within(abs=1e-3))], [sv.equivalent(floats="plan")], []):
    rep4 = sv.verify(
        feat2,
        requires={"readings": [_.temp_c.between(-90, 60), _.sensor.notnull(), sv.max_rows(10_000_000)]},
        ensures=ens,
    )
    a = rep4.run(con, "duckdb")
    b = rep4.run(con, "polars")
    print(f"\nattempt 4 ensures={ens}: proved={rep4.proved}")
    print("  duckdb:", rep4.routes["duckdb"])
    print("  polars:", rep4.routes["polars"])
    print("  observation:", rep4.observation, "equal:", rep4.observation.equal(a, b))
