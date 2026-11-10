# sverify-duckdb

Sverify-duckdb is a working prototype, and so is sverify, which it extends.
Their proofs and code still need a human audit before anyone relies on their
results.

DuckDB as an engine of [sverify](https://github.com/AlexanderNenninger/substrait-lean),
its default one: a plan verified in Lean is written as DuckDB SQL through a
lowering proved for every plan, and runs on the process's DuckDB database.
`pip install sverify` installs it with DuckDB (`sverify-duckdb[run]`): for now
sverify's table store runs on DuckDB, so the base needs it. sverify finds it
through its `ProfilePlugin` in the entry-point group `sverify.profiles`.

The directory is one engine package of #1189:

- `src/sverify_duckdb/`: the plugin (`PLUGIN`) with the table store
  (`DuckDBStore`), the dialect (`dialect`: `DUCKDB`) and the runner (`engine`);
- `facts/`: what DuckDB does at each of the core's options, the evidence for
  `Profile.duckdb` ([facts/README.md](facts/README.md));
- `replay/`: the replay of DuckDB's sqllogictests, one ledger per area, the
  fuzz findings and the probes the facts cite;
- `tests/`: its tests, which run in sverify's test session
  (`python/pyproject.toml`'s `testpaths`);
- `Sverify/DuckDB/` and `lakefile.toml`: its Lean half, the Lake package
  `sverify-duckdb`: `Profile.duckdb` and the SQL printer's model, the black
  boxes, the choice table, the lowering (its generated entries and the
  lemmas they compute with) and `Engine.duckdb`, on the core, the analysis
  and engines-common alone ([docs/proofs.md](../../docs/proofs.md)). The
  lift follows once its parser has a package.
