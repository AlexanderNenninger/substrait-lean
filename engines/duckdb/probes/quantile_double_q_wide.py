import random

import duckdb

con = duckdb.connect()
con.execute("SET threads=1")
con.execute("CREATE TABLE t(x DOUBLE)")
con.execute("INSERT INTO t VALUES (0.0), (1.0)")
random.seed(15302)
for scale in (19, 22, 23, 30, 37, 38):
    off = err = 0
    first = None
    for _ in range(2000):
        num = random.randrange(1, 10**scale)
        q = f"0.{num:0{scale}d}"
        try:
            g = con.execute(f"SELECT quantile_cont(x, {q}) FROM t").fetchall()[0][0]
        except Exception as e:  # noqa: BLE001
            err += 1
            first = first or (q, type(e).__name__, str(e)[:80])
            continue
        if g != float(q):
            off += 1
            first = first or (q, repr(g), repr(float(q)))
    print("scale", scale, "of 2000: differ", off, "errors", err, "first", first)
