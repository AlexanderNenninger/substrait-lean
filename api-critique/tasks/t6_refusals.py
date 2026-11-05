"""Task 6: react to a refusal and to an inferred precondition.

A margin column (a division) and a scaled price (a multiplication), then the
knobs: on_inferred, infer, strict, on_unproved; then composition.
"""

import inspect
import warnings

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.errors import CompositionError, PreconditionError, VerificationError
from sverify.io import StaticSource

items = StaticSource(
    pa.table({"sku": [1, 2, 3], "price": [500, 1200, 80], "cost": [300, 1300, 0], "qty": [2, 1, 5]}),
    name="items",
)


def margins(items):
    return items.select(
        items.sku,
        margin_pct=(items.price - items.cost) * 100 // items.price,
        revenue=items.price * items.qty,
    )


# 1. No requires: what does the error tell me?
t1 = sv.transform(ensures=[_.revenue >= 0])(margins)
try:
    items.pipe(t1)
except VerificationError as e:
    print("1. refused:\n", e)

# 2. Can I get the needed preconditions as code and paste them?
try:
    t1(items)
except VerificationError as e:
    report = getattr(e, "report", None)
    print("\n2. e.report:", type(report).__name__)
    if report is not None:
        print("   needed:", report.needed)
        print("   needs_lines():", report.needs_lines() if callable(report.needs_lines) else report.needs_lines)
        print("   suggestions:", report.suggestions)

# 3. on_inferred="warn": does it run?
t3 = sv.transform(ensures=[_.revenue >= 0], on_inferred="warn")(margins)
with warnings.catch_warnings(record=True) as w:
    warnings.simplefilter("always")
    try:
        node = items.pipe(t3)
        print("\n3. on_inferred=warn: built; warnings:", [str(x.message)[:300] for x in w])
        print(node.refresh())
    except Exception as e:
        print(f"\n3. on_inferred=warn: {type(e).__name__}: {str(e)[:600]}")

# 4. infer=False beside on_inferred: which wins?
for kw in [dict(infer=False), dict(infer=False, on_inferred="silent"), dict(strict=True)]:
    try:
        t4 = sv.transform(ensures=[_.revenue >= 0], **kw)(margins)
        items.pipe(t4)
        print(f"\n4. {kw}: proved")
    except Exception as e:
        print(f"\n4. {kw}: {type(e).__name__}: {str(e)[:400]}")

print("\nhelp on strict / infer / on_inferred / check_requires:")
doc = inspect.getdoc(sv.transform)
for key in ("strict", "infer", "on_inferred", "check_requires", "engine"):
    hits = [ln for ln in doc.splitlines() if key in ln]
    print(f"  {key}: {hits[:2]}")

# 5. Declare what was asked; a bad row arrives.
t5 = sv.transform(
    requires={"items": [_.price > 0, _.price < 10**12, _.cost >= 0, _.cost < 10**12, _.qty >= 0, _.qty < 10**6]},
    ensures=[_.revenue >= 0],  # _.margin_pct <= 100 is not provable (relation between columns)
)(margins)
node = items.pipe(t5)
print("\n5.", t5.last_report)
node.refresh()
items.apply(sv.Changes(inserts=[(4, 0, 10, 1)]))
try:
    node.refresh()
except PreconditionError as e:
    print("5. bad row:", e)
    print("   attrs:", [a for a in dir(e) if not a.startswith("_")])


# 6. Composition: downstream needs margin_pct >= 0, upstream doesn't promise it.
@sv.transform(requires={"m": [_.margin_pct >= 0]}, ensures=[_.margin_pct >= 0])
def healthy(m):
    return m.filter(m.revenue > 100)


try:
    node.pipe(healthy)
except CompositionError as e:
    print("\n6. composition:", e)
except VerificationError as e:
    print("\n6. (VerificationError, not CompositionError):", e)
