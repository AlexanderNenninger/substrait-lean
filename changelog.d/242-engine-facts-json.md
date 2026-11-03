### Engine facts as JSON documents, with provenance

What DuckDB does, judged against the reference semantics, is now one JSON
document per finding in `characterization/duckdb/facts/`, in the format of
`characterization/fact.schema.json`: the engine version checked, what the
engine and the reference do, a status, and each check's date, method, tool
and evidence (DuckDB's tests at their commit, the replay ledgers, the probe
verdicts of `probes.json`). DataFusion 51's findings from the replay are in
`characterization/datafusion/facts/`. `characterization/<engine>/FACTS.md`
is generated from them by `python -m sverify_dev.facts --write`.
