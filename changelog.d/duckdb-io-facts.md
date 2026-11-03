### Engine facts: JSON only, and an `io` layer

The facts in `characterization/<engine>/facts/` are the record: the generated
`FACTS.md` overviews, `python -m sverify_dev.facts --write` and their step in
the `Generated files` workflow are gone; `python -m sverify_dev.facts` checks the
documents. `fact.schema.json` has a layer and an area `io` (how an engine reaches
data: extensions, catalogs, object stores, credentials) and a status
`workaround`. The first: DuckDB's `unity_catalog` extension's ATTACH ignores a
named secret unless it names it (`duckdb-IO1`) and ignores the vended `endpoint_url`, so a
MinIO behind Unity Catalog needs DuckDB's `s3_endpoint` settings (`duckdb-IO2`);
its `delta` reader is then denied with the table-scoped keys (`duckdb-IO3`, open).
