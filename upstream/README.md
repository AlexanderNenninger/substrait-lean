# Upstream bugs

Bugs and surprising behaviours that sverify found in the projects it builds
on: SQLGlot, the engines (DuckDB, Polars, Spark), Ibis, delta-rs and
Substrait's tooling, and DataFusion, which it ran until it was dropped. We file them upstream in batches, so each one
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
checked against the latest upstream release), `confirmed` (reproduces on the
latest release or main, and no upstream issue reports it: ready to report),
`filed` (with the link in `upstream`), `fixed upstream` (fixed on the
project's main, with the release in `fixed_in`, marked unreleased until it
ships), `duplicate` (an open upstream issue covers it, linked in `upstream`;
a comment there is all it needs) or `not a bug` (documented or intended, or a
difference only sverify's model cares about, which an engine fact records;
the reason in `status_note`). `checked` records when an entry was last
checked, and against which releases. On 2026-11-07 every entry was
classified, and each that was not filed, fixed or declared intended was run
again on the latest release (sqlglot 30.30.0, duckdb 2.0.0, polars 2.1.0,
pyspark 4.3.0, ibis-framework 12.0.0, deltalake 1.6.6) or checked against
Substrait's main; its last `checked` entry says what. A `confirmed` bug has a
one-line `title`.

Sverify no longer runs DataFusion. The `DF` entries, found on DataFusion 51,
are the record of its bugs, and they are worth reporting.

The documents are the record. `REPORT.md`, generated from them on
`main`, lists the bugs to report and counts each class (report, filed,
fixed, duplicate, not-a-bug, spec-gap) by project; feature branches don't
commit it. `python -m sverify_dev.bugs` checks the documents
(`python/tests/test_bugs.py` runs the same check), and with `--write` renders
the report. The `upstream-report` skill
(`.claude/skills/upstream-report/`) drafts a report from a document.
