### Spark as a profile

`verify(semantics="spark")` checks an Ibis transformation under Spark's
profile, and its plan runs on Spark by the route `native`, in `Report.run`
and in `Node.refresh(engine="spark")`
([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)).

- Spark 4.3.0's choices, from its facts, are a table of the checker
  (`substrait-check --options`), so a plan verified under the reference
  reaches Spark with its class and the shims it needs named, and one verified
  under Spark's profile transfers to DuckDB where the choices allow it.
- The shims are proved in Lean (`engines/spark/Sverify/Spark/Shims.lean`), with
  `Rel.spark_sound`: a verified plan, as `sverify_spark.dialect` writes it, gives
  the reference's rows on Spark under ANSI mode.
- A run reads the Spark session's settings and refuses one that changes
  what the profile relies on (ANSI mode, the timestamp type, the session
  time zone, …), naming the setting and how to restore it; another Spark
  version warns, another major version is refused.
- `MIN` and `MAX` of doubles run on Spark.
- Tables go to Spark as Arrow: a table of a million rows registers in a
  twentieth of the time, and no Python worker starts.
