### Window variance, unordered STRING_AGG, signed Ibis frame offsets, divisor suggestions

`VARIANCE` and `STDDEV` (of a sample or a population) now verify over a
window ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)).
Over a frame they are the reference's own two passes, which DuckDB runs
exactly; other engines refuse them for now (#271).

`group_concat()` / `STRING_AGG` without an order verifies: the strings may come
in any order, so `verify` reports the plan as not deterministic and proves no
postcondition about it. DuckDB joins them in the input's order.

Ibis windows with a negative offset count the other way, as Ibis means them:
`following=-1` is `1 PRECEDING`. Ibis's own SQL writes `-1 FOLLOWING`, which
DuckDB refuses ([IB-4](upstream/bugs/IB-4.json)).

`verify` now proposes a precondition for a division by an aggregate: each value
at least 1 (or 0.01 for a decimal) for a `SUM`, and the column NOT NULL for a
grouped `COUNT` (`_.size >= 1`, `_.user_id.notnull()`).
