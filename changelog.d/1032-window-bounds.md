### Window sums of doubles have the plan's bound

- A window `SUM` or `AVG` of doubles has a bound again: `Report.epsilon`
  gives its column the bound of the input's row cap, as for a grouped one,
  proved under the same conditions
  ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  It rests on each engine's window algorithm, a new option
  (`window_sum_algo`) with a fact per engine: DuckDB, Polars and Spark sum
  each frame's own values (a tree, each frame anew, or a running sum). A
  window `VARIANCE` or `STDDEV` still has no bound (#918). Snowflake refuses a
  window `SUM` or `AVG` of doubles until its window algorithm has a fact.
- The options a plan depends on include its windows' sort keys and partition
  keys. A window over a key now takes its evidence from the engine's NULL
  placement row.
