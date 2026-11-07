### A LIMIT without an ORDER BY says how to fix its refresh

A `refresh` refuses a plan whose `LIMIT` has no `ORDER BY`, since a rerun may
take other rows, and the refusal now says to order the rows before the
`LIMIT` by a key ([#928](https://github.com/AlexanderNenninger/substrait-lean/issues/928)).
`verify` and `run` allow such a plan, and the proofs hold for every choice of
rows (`Rel.Bags`, `SubstraitLean/Seam.lean`). A route reads DuckDB's settings
in one query (0.86 ms to 0.25 ms).
