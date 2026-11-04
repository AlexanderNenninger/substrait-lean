### The realizability table (#444)

`docs/realizability.md` lists, for DuckDB and Polars and every option of
the catalogue, how a plan verified under the reference runs there: native,
after a shim (with its cost), up to an observation, within a float bound,
behind a precondition the reference raises on, or refused, with the theorem
or facts each row rests on, and the shim count per engine. It is generated
from `substrait-check --realizability` (`SubstraitLean/Obligations.lean`)
by `python -m sverify_dev.realizability --write`, and
`tests/test_realizability.py` checks it is current. `Rel.duckdb_refines`
states DuckDB's translation as a refinement of the reference, raise sets
included (`Lowering.lowerRel_raises`). `substrait-check --dependencies` now
lists the Polars `null_order` shim only for a key that leaves its NULL
placement unspecified.
