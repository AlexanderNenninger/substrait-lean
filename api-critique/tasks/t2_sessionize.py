"""Task 2: sessionize click events: a new session after 30 minutes of quiet.

Window functions (LAG, a running sum), then one row per session.
"""

import datetime as dt

import ibis
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.errors import VerificationError

t0 = dt.datetime(2026, 11, 5, 9, 0)
mins = [0, 5, 50, 52, 0, 100]
clicks_data = pa.table(
    {
        "user_id": [1, 1, 1, 1, 2, 2],
        "ts": [t0 + dt.timedelta(minutes=m) for m in mins],
        "page": ["a", "b", "c", "d", "a", "b"],
    }
)

con = sv.connect()
con.put("clicks", clicks_data)
clicks = con.table("clicks")


def sessionize(t):
    w = ibis.window(group_by=t.user_id, order_by=t.ts)
    prev = t.ts.lag().over(w)
    new = ibis.cases((prev.isnull(), 1), (t.ts - prev > ibis.interval(seconds=1800), 1), else_=0)
    flagged = t.mutate(new_session=new)
    w2 = ibis.window(group_by=flagged.user_id, order_by=flagged.ts, preceding=None, following=0)
    return flagged.mutate(session_no=flagged.new_session.sum().over(w2))


# Attempt 1: the natural contract.
expr = sessionize(clicks)
r = sv.verify(
    expr,
    requires={"clicks": [_.user_id.notnull(), _.ts.notnull(), sv.unique("user_id", "ts")]},
    ensures=[_.session_no >= 1, _.new_session.isin([0, 1])],
)
print("attempt 1 proved:", r.proved)
print(r)

# Attempt 2: follow what the report asks.
if not r.proved:
    print("\n--- needs_text:", r.needs_text if hasattr(r, "needs_text") else None)

r2 = sv.verify(
    expr,
    requires={
        "clicks": [
            _.user_id.notnull(),
            _.ts.notnull(),
            _.ts >= dt.datetime(1900, 1, 1),
            _.ts < dt.datetime(2200, 1, 1),
            sv.unique("user_id", "ts"),
            sv.max_rows(10**9),
        ]
    },
    ensures=[_.session_no >= 1, _.new_session >= 0, _.new_session <= 1],
)
print("attempt 2 proved:", r2.proved)
print(r2)
if r2.proved:
    print(r2.run(con).to_pylist()[:3])
    print(r2.run(con, "polars").to_pylist()[:3])
    print(r2.routes)

# Attempt 3: one row per session, as a transform.
@sv.transform(
    requires={
        "clicks": [
            _.user_id.notnull(),
            _.ts.notnull(),
            _.ts >= dt.datetime(1900, 1, 1),
            _.ts < dt.datetime(2200, 1, 1),
            sv.unique("user_id", "ts"),
            sv.max_rows(10**9),
        ]
    },
    ensures=[sv.unique("user_id", "session_no"), _.clicks >= 1, _.ended >= _.started],
)
def sessions(clicks):
    s = sessionize(clicks)
    return s.group_by(["user_id", "session_no"]).aggregate(
        started=s.ts.min(), ended=s.ts.max(), clicks=s.count()
    )


try:
    sessions(clicks)
    print(sessions.last_report)
except VerificationError as e:
    print("attempt 3 refused:\n", e)

# Attempt 4: run the unproved report anyway, and the proved transform on both engines.
try:
    r2.run(con)
except Exception as e:
    print(f"\nrun of unproved report: {type(e).__name__}: {e}")
print(r2.run(con, unverified=True).num_rows, "rows with unverified=True")

from sverify.io import StaticSource

src = StaticSource(clicks_data, name="clicks")
node = src.pipe(sessions)
print(node.refresh(engine="polars"))
print(sorted(node.to_arrow().to_pylist(), key=lambda r: (r["user_id"], r["session_no"])))
src.apply(sv.Changes(inserts=[(1, t0 + dt.timedelta(minutes=55), "e")]))
print(node.refresh(engine="polars").summary())
print(node.status())
