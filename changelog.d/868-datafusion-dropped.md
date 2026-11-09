### DataFusion is no longer supported

Breaking: sverify no longer runs plans on DataFusion. The `datafusion` extra
is gone, so `pip install 'sverify[datafusion]'` fails; `engine="datafusion"`
raises "unknown engine"; and `sverify.engines.run_substrait_json`, the
checker's `--write-datafusion` and `ProfilePlugin.optional` are removed. Run
plans on DuckDB, Polars or Spark, or export them for any Substrait consumer
with `Report.to_substrait`. The DataFusion bugs sverify found stay recorded
in `upstream/bugs/DF-*.json`
([#868](https://github.com/AlexanderNenninger/substrait-lean/issues/868)).
