### A Polars or Spark run no longer runs the plan on DuckDB first

A report with assumed issues (an integer `SUM` that must fit, an operation on finite doubles that must not give `±∞`) ran its plan on DuckDB before the target engine to check them, which doubled the run and made DuckDB's errors everyone's. The Polars and Spark translations check them as they run, so `Report.run` runs the plan on the target engine only, and a batch that breaks one is refused with the same `PreconditionError` (#1484). An engine plugin says it does so with `ProfilePlugin.checks_assumed`.
