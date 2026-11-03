### Fixed: Ibis's DuckDB `create_table` failed on a fresh install

A fresh install resolved SQLGlot 30.18 or later, from which SQLGlot reads a
`DROP`'s names where Ibis 12 doesn't put them, so `con.create_table(...)` on
Ibis's DuckDB backend raised a DuckDB syntax error. sverify now requires
`sqlglot~=30.17.0` until Ibis follows
([upstream/LEDGER.md](../upstream/LEDGER.md) SG-7, #442).
