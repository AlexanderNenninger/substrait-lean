# sverify-spark

Sverify-spark is a working prototype, and so is sverify, which it extends.
Their proofs and code still need a human audit before anyone relies on their
results.

Spark as an engine of [sverify](https://github.com/AlexanderNenninger/substrait-lean):
a plan verified in Lean is written as Spark SQL, with a shim where Spark
differs from the reference, and runs on a Spark session under ANSI mode.
`pip install sverify[spark]` installs it with PySpark; `sverify-spark` alone
writes Spark SQL (`sverify_spark.dialect.SPARK`) without PySpark. sverify finds
it through its `ProfilePlugin` in the entry-point group `sverify.profiles`.

The directory holds the whole engine package:

- `src/sverify_spark/`: the plugin (`PLUGIN`), the dialect (`dialect`:
  `SPARK`, `SPARK_CONF`) and the runner on a Spark session (`engine`);
- `facts/`: what Spark does at each of the core's options, the evidence for
  `Profile.spark` ([facts/README.md](facts/README.md));
- `probes/`: the probes' and the fuzzer's recordings the facts cite;
- `tests/`: its tests, which run in sverify's test session
  (`python/pyproject.toml`'s `testpaths`);
- `Sverify/Spark/` and `lakefile.toml`: its Lean half, the Lake package
  `sverify-spark`: the choice table, the shims and their lemmas,
  `Profile.spark` and the `Engine` value, on the core, the analysis and
  engines-common alone ([docs/proofs.md](../../docs/proofs.md)).
