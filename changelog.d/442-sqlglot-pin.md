### Fixed: Ibis's DuckDB `create_table` failed on a fresh install

A fresh install resolved SQLGlot 30.18 or later, which writes Ibis 12's
`DROP VIEW IF EXISTS` without the view's name, so `con.create_table(...)` on
Ibis's DuckDB backend raised a DuckDB syntax error. sverify now requires
`sqlglot>=30.0.0,<30.18` until Ibis or SQLGlot fixes it
([upstream/LEDGER.md](../upstream/LEDGER.md) SG-7, #442).
