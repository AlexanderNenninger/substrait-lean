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
