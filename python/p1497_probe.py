import ibis, sverify as sv
import ibis.expr.datatypes as dt
from sverify.ibis_substrait.core import DecimalDiv

T = ibis.table({"a": "decimal(10,2)"}, name="t")
one = ibis.literal(1, "int64").op()
q = T.select(r=DecimalDiv(T.a.op(), one, dt.Decimal(5, 2)).to_expr())
r = sv.verify(q, on_inferred="off")
print("VERDICT", r.verdict, [(i.kind) for i in r.errors])
for d in ("duckdb", "polars", "spark"):
    try:
        print(d, "SQL", r.to_sql(d)[:300])
    except Exception as e:
        print(d, "ERR", type(e).__name__, str(e)[:500])
