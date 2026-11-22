# Sessionize: gaps and islands

Use it to split a user's events into sessions at a gap, or to number runs of
consecutive rows.

## The rule

An event starts a session when it is the user's first or follows the previous
one by more than the gap. A running sum of the starts numbers the sessions.

```python
import ibis
from ibis import _

import sverify as sv

clicks = ibis.table({"user": "string", "ts": "int64"}, name="clicks")
by_user = ibis.window(group_by=clicks.user, order_by=clicks.ts)
step = clicks.mutate(prev=clicks.ts.lag().over(by_user))
step = step.mutate(new=ibis.ifelse(step.prev.isnull() | (step.ts - step.prev > 1800), 1, 0))
running = ibis.window(group_by=step.user, order_by=step.ts, rows=(None, 0))
sessions = step.mutate(session=step.new.sum().over(running)).select("user", "ts", "session")
```

In SQL:

```sql
WITH g AS (SELECT user, ts, lag(ts) OVER (PARTITION BY user ORDER BY ts) AS prev FROM clicks),
n AS (SELECT user, ts, CASE WHEN prev IS NULL OR ts - prev > 1800 THEN 1 ELSE 0 END AS new FROM g)
SELECT user, ts, sum(new) OVER (PARTITION BY user ORDER BY ts
  ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) AS session FROM n
```

## The contract

`(user, ts)` is a key of the output, and a session number is never negative.
A window's value is nullable to the proof, so the postcondition allows NULL.

```python
requires = {
    "clicks": [
        _.user.notnull(),
        _.ts.notnull(),
        _.ts >= 0,
        _.ts < 2**40,
        sv.unique("user", "ts"),
    ]
}
ensures = [_.session.isnull() | (_.session >= 0), sv.unique("user", "ts")]
assert sv.verify(sessions, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

- `session >= 1` is unproved: the proof does not know the first event starts a
  session. State the weaker form above.
- Without the key `unique(user, ts)` two events at the same instant tie, and
  the report says which key closes it.
- `ts - prev` needs a bound on `ts` (`_.ts < 2**40`), which `--fix` suggests.
