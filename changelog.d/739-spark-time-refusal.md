### Spark's refusal of a time of day names the setting

A plan with a time of day (`TIME`) refused on Spark now says why: Spark 4.3 reads `TIME` only with `spark.sql.timeType.enabled` on (spark-time-type). The old message said `TIME` needed Spark 4.1 and named the internal kind `tod` ([#739](https://github.com/AlexanderNenninger/substrait-lean/issues/739)).
