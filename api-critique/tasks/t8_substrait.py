"""Task 8: export a verified plan with to_substrait() and hand it to another consumer.

A data engineer wants the checked plan as a file that another engine
(DataFusion's Substrait consumer, or a service) can run.
"""

import json
import pathlib
import tempfile

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.errors import ExportError
from sverify.io import StaticSource

con = sv.connect()
con.put("orders", pa.table({"id": [1, 2, 3], "qty": [4, 5, 2], "total": [100, 250, 30], "w": [0.5, 1.5, 2.0]}))
t = con.table("orders")
REQ = {"orders": [_.qty > 0, _.total >= 0, _.total < 10**9, _.w.between(0, 10), sv.max_rows(10**6)]}

# 1. From a report.
rep = sv.verify(t.select(t.id, unit=t.total // t.qty), requires=REQ, ensures=[_.unit >= 0])
plan = rep.to_substrait()
print("type:", type(plan).__name__, "length:", len(plan))
doc = json.loads(plan)
print("top-level keys:", list(doc))
out = pathlib.Path(tempfile.mkdtemp()) / "unit.substrait.json"
out.write_text(plan)
print("round trip proved:", sv.from_substrait(out.read_text()).proved)

# 2. From a transform / node: is there a to_substrait there?
src = StaticSource(pa.table({"id": [1], "qty": [1], "total": [1], "w": [1.0]}), name="orders")


@sv.transform(requires=REQ, ensures=[_.unit >= 0])
def unit(orders):
    return orders.select(orders.id, unit=orders.total // orders.qty)


node = src.pipe(unit)
for obj, name in [(node, "Node"), (unit, "transform"), (unit.last_report, "transform.last_report")]:
    print(f"{name}.to_substrait:", hasattr(obj, "to_substrait"))
print("node.plan type:", type(node.plan).__name__, "(is it Substrait?)", str(node.plan)[:80])

# 3. Doubles: a mean with a tolerance; a comparison of doubles.
for label, expr, ens in [
    ("mean", t.group_by("qty").aggregate(m=t.w.mean()), [sv.equivalent(floats=sv.within(abs=1e-6))]),
    ("filter on a double", t.filter(t.w > 1.0).select("id", "w"), []),
    ("upper()", t.select(t.id, s=t.id.cast("string").upper()), []),
]:
    r = sv.verify(expr, requires=REQ, ensures=ens)
    try:
        r.to_substrait()
        m = r.substrait_contract()["manifest"]
        print(f"\n{label}: exported; class={m['class']} evidence={m['evidence']} shims={[s['shim'] for s in m['shims']]}")
    except ExportError as e:
        print(f"\n{label}: ExportError: {e}")

# 4. Run the export somewhere: does sverify run Substrait JSON itself?
from sverify import engines

print("\nengines.run_substrait_json:", engines.run_substrait_json.__doc__.splitlines()[0])
try:
    res = engines.run_substrait_json(con, plan)
    print("ran:", res)
except Exception as e:
    print(f"run_substrait_json(con, plan): {type(e).__name__}: {str(e)[:300]}")

# 5. An engine profile's report.
r_duck = sv.verify(t.select("id", "total"), semantics="duckdb")
try:
    r_duck.to_substrait()
except ExportError as e:
    print("\nsemantics=duckdb export:", e)
