### Examples and searchable ledgers on the docs site

The docs site has two new sections. Examples
([docs/examples.md](docs/examples.md)) shows sverify's features in eight short
steps: a contract proved and run, SQL through `sv.verify`, inferred
preconditions refusing a bad batch before the run, routes to Polars and their
classes, doubles within a tolerance, a reproducible sink kept up to date,
a plan checked under DuckDB's profile, and Substrait's own semantics. Ledgers
renders the upstream ledger (bugs and Substrait spec gaps), DuckDB's and
Polars's characterization facts, the checklist's coverage per engine and the
realizability table from their JSON at build time, one anchor per entry, so
the site's search finds an entry by id, engine, function, option or text, and
the ledgers' index filters them. The README and the tour's notebooks describe
routes, observations, reproducible sinks, the inputs checked before a run and
the stricter reference.
