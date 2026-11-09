### Spark is a package of its own: sverify-spark

sverify's Spark engine moves into the distribution `sverify-spark`
(`engines/spark/`, package `sverify_spark`), released with sverify at its
version ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`pip install sverify[spark]` installs it with PySpark. It registers its
`ProfilePlugin` in the entry-point group `sverify.profiles` as a package from
outside does. Spark's facts, probes and fuzz findings move with it, to
`engines/spark/facts/` and `engines/spark/probes/`.

The Spark SQL dialect moves with the engine: `sverify.engines.SPARK` and
`sverify.engines.SPARK_CONF` are now `sverify_spark.dialect.SPARK` and
`sverify_spark.dialect.SPARK_CONF`, and `to_sql(plan, "spark")` needs
`sverify-spark` installed. `sverify.engines.run_spark`, deprecated since 0.5,
is gone: write `sverify.engines.run(con, plan, "spark")`, or pass your own
Spark session in place of `"spark"`.
