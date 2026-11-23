### The replay skips queries DuckDB's time limit interrupts

The DuckDB replay (`sverify_dev.slt`) skips a query that DuckDB stops with `max_execution_time` ("Query exceeded maximum execution time"): the time limit is an outcome no model states. `function/string/test_levenshtein_interrupt.test` no longer runs Lean into the checker's watchdog, and queries that finish under the limit are replayed as before ([#2498](https://github.com/AlexanderNenninger/substrait-lean/issues/2498)).
