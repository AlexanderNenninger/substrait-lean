# Theorem cards

One page for each top-level theorem: what it says in plain language, what it
assumes, what it does not say, how the Lean statement reads line by line,
and an example you can run. Each card names the layer the theorem is stated
over (`eval`, `OrderAllowed`, `Allowed`, `AllowedP`, `Near`) and its axioms.
[proofs.md](../proofs.md) maps every guarantee to its theorem.

| Card | Says |
|---|---|
| [`contract_sound`](contract_sound.md) | A proved postcondition is TRUE on every output row |
| [`contract_sound_all`](contract_sound_all.md) | … in every row order the reference allows |
| [`contract_sound_allowed`](contract_sound_allowed.md) | … on every result the reference allows, doubles summed in any order included |
| [`contract_sound_allowed_closed`](contract_sound_allowed_closed.md) | … with the float-safety condition replaced by a check on the plan |
| [`Rel.duckdb_sound`](duckdb_sound.md) | A proved plan returns the reference's rows on DuckDB as the printer writes it |
| [`Rel.polars_sound`](polars_sound.md) | … on Polars, after the shims |
| [`Rel.spark_sound`](spark_sound.md) | … on Spark under ANSI |
| [`Rel.keys_sound`](keys_sound.md) | A derived key holds on the output: no two rows share its columns |
| [`Rel.AllowedP_mono`](allowedp_mono.md) | A profile whose choices are within another's allows no more results |
| [`Rel.refines_of_perm`](refines_of_perm.md) | A rewrite with no open choices, with the original's rows in some order, refines it |
| [`Rel.optimize_refines`](optimize_refines.md) | The optimized plan refines the original, up to the order of rows |
| [`floatSumCR_mem`](floatsumcr_mem.md) | The `SUM` of bounded doubles, with a row cap, lies within the checker's bounds |
| [`floatAvgCR_mem`](floatavgcr_mem.md) | The `AVG` of bounded doubles lies within their range, widened by the tolerance |
| [`comomentNum_nonneg`](comomentnum_nonneg.md) | A variance's numerator is never negative |
| [`Refresh.no_corruption`](refresh_no_corruption.md) | A sink's table never holds a change applied to a table it was not computed from |
| [`Refresh.record_describes_table`](refresh_record_describes_table.md) | When the node's commit is the newest, the table is the state its record names |
| [`Refresh.read_is_head`](refresh_read_is_head.md) | A change that lands applies to the newest commit of the node, computed against its table |
| [`Refresh.monotone`](refresh_monotone.md) | Adjacent commits of one plan are of later versions: no state is committed twice in a row |
| [`Refresh.quiet`](refresh_quiet.md) | Once the environment is quiet, the processes' steps reach the deployed plan's state of the source and keep it |
