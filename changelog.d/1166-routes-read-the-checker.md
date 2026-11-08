### Routes take the checker's verdict

- The class, evidence, shims and refusals of a route come from the checker's
  verdict per engine (`substrait-check --contract`'s `"engines"`), and the
  transfer route takes the checker's transfer check (`Rel.transfer_of_transferB`)
  over every option the plan reads
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
  A sort whose NULL placement the plan states now transfers to an engine that
  gives it as stated (17 catalogue plans verified under Polars's or Spark's
  semantics now reach DuckDB); an integer `SUM` verified under Spark's
  semantics no longer transfers to DuckDB, whose `avg_int_result` differs in
  the group the check reads.
- A proof of the engine's model names the facts that say the engine is that
  model: `evidence proved by Rel.polars_sound on polars's model (facts …)`.
- A report read back with `Report.from_json` keeps the checker's verdict, and
  routes as it did.
