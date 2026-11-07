### Window aggregates of doubles have the plan's bound

- A window `SUM` or `AVG` of doubles runs again, as the engine's own sum,
  and `Report.epsilon` gives its column the bound of the input's row cap, as
  for a grouped one ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  A window `VARIANCE` or `STDDEV` runs on DuckDB with no stated bound: a run
  is tested, and a tolerance on it is refused.
- The options a plan depends on include its windows' functions, sort keys
  and partition keys. A window over a key now takes its evidence from the
  engine's NULL placement row.
