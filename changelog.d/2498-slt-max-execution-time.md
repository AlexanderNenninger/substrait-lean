### The replay skips queries under max_execution_time

The DuckDB replay (`sverify_dev.slt`) skips queries run under `SET max_execution_time`, whose expected outcome is a time limit that no model states. `function/string/test_levenshtein_interrupt.test` no longer runs Lean into the checker's watchdog ([#2498](https://github.com/AlexanderNenninger/substrait-lean/issues/2498)).
