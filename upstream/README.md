# Upstream bugs

Bugs and surprising behaviours that sverify found in the projects it builds
on: SQLGlot, the engines (DuckDB, Polars, DataFusion, Spark), Ibis, delta-rs
and Substrait's tooling. We file them upstream in batches, so each one
records enough to file it: the version, a minimal reproduction, and how
sverify works around it today.

Each bug is a document `bugs/<id>.json` in the format of
[`bug.schema.json`](bug.schema.json). Add one whenever you find a bug, in the
same PR as the workaround. Engine behaviour that is documented and intended,
and differs from the reference model, goes into that engine's
characterization (`characterization/<engine>/facts/`) and profile.

Gaps in Substrait's spec are entries too, with `kind: "spec-gap"`: a behaviour
the extension YAMLs or the docs leave unstated though Substrait could express
it (an option, an option's value, a default), where engines differ. The entry
says what is unstated, how an option could express it, what each engine does
(its `facts`), and how sverify's core handles it
([core-semantics.md](../docs/core-semantics.md), D3). It is checked against
Substrait's current `main` before it is added, and stays `unverified`
until it is checked against Substrait's open issues.

The id is the project's prefix and the next free number:

| Prefix | Project |
|---|---|
| `SG` | SQLGlot |
| `DF` | DataFusion |
| `DD` | DuckDB |
| `DL` | delta-rs (`deltalake`) |
| `PL` | Polars |
| `SP` | Spark |
| `IB` | Ibis |
| `ST` | Substrait: its tooling and its spec |

The status is `unverified` (seen, not yet reduced to a minimal repro or
checked against the latest upstream release), `confirmed` (minimal repro on
the stated version), `filed` (with the link in `upstream`), `fixed upstream`
(with the release in `fixed_in`) or `not a bug` (with the reason in
`status_note`). `checked` records when an entry was last checked, and
against which releases: every entry of the old ledger was checked on 2026-11-03 against
sqlglot 30.29.0, ibis-framework 12.0.0, datafusion 55.0.0, duckdb 2.0.0 and
deltalake 1.6.6.

DataFusion is a backend only since #211. Bugs in its Substrait producer and
SQL planner (most `DF` entries, found on DataFusion 51) no longer affect
sverify's results, and they are worth reporting.

The documents are the record; there is no generated overview.
`python -m sverify_dev.bugs` checks them (`python/tests/test_bugs.py` runs
the same check). The `upstream-report` skill
(`.claude/skills/upstream-report/`) drafts a report from a document.
