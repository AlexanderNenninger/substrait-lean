### sverify-dbt checks a model that reads an ephemeral model

dbt inlines an ephemeral model into each reader as a CTE, so the reader's compiled SQL names the ephemeral's inputs. `sverify-dbt check` now reads those inputs through the ephemeral model, transitively, instead of refusing the reader with "a hard-coded table name"; the ephemeral model itself prints a note saying which models it is inlined into (#891, 1.4).
