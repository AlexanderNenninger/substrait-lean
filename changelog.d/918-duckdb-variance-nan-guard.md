### DuckDB's variance NaN guard is proved

DuckDB gives `0.0` for `VAR_POP` and `STDDEV_POP` of a lone NaN
([DD-3](upstream/bugs/DD-3.json)), where the reference gives NaN. Sverify's
SQL has returned NaN there since #54 and #1141; the DuckDB profile now names
that guard as the shim `nan_through` of its `agg.var` `stat_algo` row, with
its soundness lemma `Stat.nanGuard_varStat` (#918). `--options` and the
realizability table list it as DuckDB's fourth shim.
