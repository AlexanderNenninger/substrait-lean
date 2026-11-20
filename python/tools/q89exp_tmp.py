import sverify
from sverify_dev import catalogue as C
schemas = C.load_schemas()
q = next(x for x in C.load_queries() if x.id == "tpcds-q89")
ns = C.scope(q, schemas, "native")
exec(q.ibis, ns)
req, _ens = C.contract(q, schemas, "native")
_ = ns["_"]
def run(name, t, ens):
    try:
        r = sverify.verify(t, requires=req, ensures=ens)
        print("##", name, "proved", r._proved, "unproved", [c.label for c in r.unproved], "errors", [str(e)[:160] for e in r.errors], flush=True)
    except Exception as e:
        print("##", name, "EXC", str(e)[:300], flush=True)
m = ns["m"]; monthly = ns["monthly"]
run("A monthly sum>=0", monthly, [_.sum_sales >= 0])
run("B window avg", m, [_.avg_monthly_sales.isnull() | (_.avg_monthly_sales >= 0)])
d = m.mutate(diff=(m.sum_sales - m.avg_monthly_sales).abs())
run("C abs diff", d, [_.diff.isnull() | (_.diff >= 0)])
d2 = m.mutate(r=(m.sum_sales - m.avg_monthly_sales).abs() / m.avg_monthly_sales)
run("D ratio", d2, [_.r.isnull() | (_.r >= 0)])
