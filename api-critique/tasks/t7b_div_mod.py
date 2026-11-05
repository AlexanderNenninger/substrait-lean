"""Task 7b: does q * d + r == x hold for Ibis `//` and `%` on a negative x?"""

import pyarrow as pa
from ibis import _

import sverify as sv

con = sv.connect()
con.put("t", pa.table({"x": pa.array([-7, 7], pa.int64())}))
t = con.table("t")
req = {"t": [_.x.between(-1000, 1000)]}
for sem in ("reference", "duckdb", "polars"):
    rep = sv.verify(t.select(t.x, q=t.x // 2, r=t.x % 2), requires=req, semantics=sem)
    for eng in ("duckdb", "polars"):
        try:
            rows = rep.run(con, eng).to_pylist()
            print(sem, eng, rows, "q*2+r==x:", all(row["q"] * 2 + row["r"] == row["x"] for row in rows))
        except Exception as e:
            print(sem, eng, type(e).__name__, str(e)[:120])
sq = sv.verify("SELECT x, x // 2 AS q, x % 2 AS r FROM t", tables={"t": t}, requires={"t": ["x BETWEEN -1000 AND 1000"]})
print("SQL reference duckdb", sq.run(con).to_pylist())
print("plain duckdb:", con.ibis.raw_sql("SELECT -7 // 2, -7 % 2").fetchall())
