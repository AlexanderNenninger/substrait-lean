# sverify-spark

Spark as an engine of [sverify](https://github.com/AlexanderNenninger/substrait-lean):
a plan verified in Lean is written as Spark SQL, with a shim where Spark
differs from the reference, and runs on a Spark session under ANSI mode.
`pip install sverify[spark]` installs it with PySpark; `sverify-spark` alone
writes Spark SQL (`sverify_spark.dialect.SPARK`) without PySpark. sverify finds
it through its `ProfilePlugin` in the entry-point group `sverify.profiles`.

The directory is one engine package of #1189:

- `src/sverify_spark/`: the plugin (`PLUGIN`), the dialect (`dialect`:
  `SPARK`, `SPARK_CONF`) and the runner on a Spark session (`engine`);
- `facts/`: what Spark does at each of the core's options, the evidence for
  `Profile.spark` ([facts/README.md](facts/README.md));
- `probes/`: the probes' and the fuzzer's recordings the facts cite;
- `tests/`: its tests, which run in sverify's test session
  (`python/pyproject.toml`'s `testpaths`).

Its Lean half (the profile and the lowering, `Sverify.Spark`) follows.
