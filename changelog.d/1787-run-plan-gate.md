### Proved rewrites can run, rule by rule

Sverify can now run the rewritten plan in place of the plan you wrote, where
the checker proves the rewrite keeps the guarantee
([#1787](https://github.com/AlexanderNenninger/substrait-lean/issues/1787),
item 2). A gate turns each rewrite rule on or off, and a rule goes on only
with a measured gain and no loss on DuckDB, Polars or Spark
(`docs/optimizations.md`, "The gate"). `Report.run` and `Report.to_sql` take the
checker's plan to run on the translated and transfer routes. Elsewhere they run
the plan as written, as they do wherever a gate keeps it: the report names that
gate. Every rule starts off, so no result or written SQL changes.
