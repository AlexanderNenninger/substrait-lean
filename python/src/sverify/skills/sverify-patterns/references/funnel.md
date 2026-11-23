# Funnel, cohort and retention

Use it to count distinct users per step, per cohort or per week.

## The rule

Group by the step and count distinct users. A cohort or retention table is the
same shape with the cohort and the week as keys.

```python
import ibis
from ibis import _

import sverify as sv

events = ibis.table({"user": "string", "step": "string"}, name="events")
funnel = events.group_by("step").aggregate(users=events.user.nunique())
```

In SQL:

```sql
SELECT step, count(DISTINCT user) AS users FROM events GROUP BY step
```

## The contract

One row per step, and a count is never negative. A `max_rows` cap bounds the
counts, so no overflow is possible.

```python
requires = {"events": [_.user.notnull(), _.step.notnull(), sv.max_rows(10**9)]}
ensures = [_.users >= 0, sv.unique("step")]
assert sv.verify(funnel, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED

sql = sv.sql("SELECT step, count(DISTINCT user) AS users FROM events GROUP BY step", events=events)
assert sv.verify(sql, requires=requires, ensures=ensures).verdict == sv.Verdict.PROVED
```

## Refusals and suggestions

- A conversion rate is a ratio of two counts. A division by a count that may be
  zero is listed under `issues`: guard it with `ibis.ifelse(den > 0, ...)`.
- `users[step n] <= users[step n-1]` relates two rows. The proof covers each
  row, so check it on the data with a test.
