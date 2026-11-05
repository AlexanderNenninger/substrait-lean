### Smaller written SQL

Sverify binds the arguments that its guards would copy to columns before it
writes a plan (`SubstraitLean/Bind.lean`, #821): a nested date or double
operation, or an aggregate's argument, is computed once in a projection
below and read by name. The `month end` query of #821 drops from 51 kB of
Spark SQL to 7 kB, and the catalogue's largest Snowflake statement from
547 kB to 16 kB. `Rel.evalI_bindArgs` and `Rel.raises_bindArgs` prove
that the plan computes the same rows and raises the same errors on every
engine.
