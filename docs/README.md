# A map of the docs

Every page of sverify's docs is one of four kinds, and each kind has one job:

- a tutorial teaches by doing, start to finish;
- a how-to guide solves one task;
- a reference states the facts, to look up;
- an explanation says how and why.

Each topic has one home, and the other pages link to it.
The [docs site](https://alexandernenninger.github.io/substrait-lean/) renders
the pages marked "site", in the section named; the rest are read here. The
pages for contributors, last, are records of the project's design: they keep
its decision numbers and issue links, and the site leaves them out.
`tests/test_docs_pages.py` checks that this map lists every page of `docs/`
and every notebook once, and `tests/test_docs_paths.py` that their links resolve and that no page
names the old place of the engine facts.

## Entry pages

| Page | For | Site |
|---|---|---|
| [python/README.md](../python/README.md) | users: what sverify does, install, a first contract | landing page |
| [README.md](../README.md) | contributors: the parts, the Lean project, development | |
| [dbt/README.md](../dbt/README.md) | analytics engineers: sverify-dbt | |
| [templates/pipelines/README.md](../templates/pipelines/README.md) | platform teams: the pipelines template | |

## Tutorial

| Page | Job |
|---|---|
| [getting-started.md](getting-started.md) | From the install to a proved plan, in ten steps; what goes wrong without a checker; how it works, in brief (on the site: Getting started) |
| [notebooks/01_duplicate_payments.py](../notebooks/01_duplicate_payments.py) | A Delta pipeline that catches double charges |
| [notebooks/02_sensor_alerts.py](../notebooks/02_sensor_alerts.py) | An Iceberg pipeline of sensor alerts: ties, NaN, windows |
| [notebooks/03_orders_mart.py](../notebooks/03_orders_mart.py) | An orders mart: a point-in-time join, dbt's tests as a contract |
| [notebooks/04_contracts.py](../notebooks/04_contracts.py) | Contracts in depth: keys, relations, runtime errors, composition |
| [notebooks/05_pipelines_and_engines.py](../notebooks/05_pipelines_and_engines.py) | Pipelines and engines: delta rules, quarantine, routes, doubles |
| [notebooks/06_running_in_production.py](../notebooks/06_running_in_production.py) | Running it in production: the command in CI, tests, credentials, lineage, late rows |
| [notebooks/07_engines.py](../notebooks/07_engines.py) | Engines: one proved plan on DuckDB, Polars and Spark, SQL for a warehouse, refusals and their exits |
| [notebooks/08_dbt.py](../notebooks/08_dbt.py) | Your dbt project: the tests sverify-dbt proves before the models run, a counterexample, `--selectors` |

The notebooks run on molab from the `published` branch, which follows the
release on PyPI.

## How-to

A page of this kind runs its Python examples in `tests/test_readme.py`, and the test fails a page of more than 600 lines (a tutorial or how-to page) or `python/README.md` of more than 90, two screens.

| Page | Job | Site |
|---|---|---|
| [tasks.md](tasks.md) | The index of the how-to pages, with the setup their examples share | |
| [how-to-contracts.md](how-to-contracts.md) | State what a transform assumes and promises, and read the report | |
| [how-to-guards.md](how-to-guards.md) | Runtime errors and the guards that rule them out | |
| [how-to-bounds.md](how-to-bounds.md) | Inferred bounds, row caps, non-overlapping ranges, rows per key and suggested preconditions | |
| [how-to-command-line.md](how-to-command-line.md) | Checking without running, `sverify check`, its formats and exit codes, the environment variables | |
| [how-to-nodes.md](how-to-nodes.md) | Nodes, composing contracts, refresh | |
| [how-to-quarantine.md](how-to-quarantine.md) | What a refresh does with rows that break a precondition | |
| [how-to-table-formats.md](how-to-table-formats.md) | A complete job in outline, and Delta Lake and Iceberg sources and sinks | |
| [how-to-credentials.md](how-to-credentials.md) | Named secrets and what each node uses | |
| [how-to-openlineage.md](how-to-openlineage.md) | Lineage events with the contract | |
| [how-to-time-buckets.md](how-to-time-buckets.md) | Bounded state for late-arriving streams | |
| [how-to-engines-and-sql.md](how-to-engines-and-sql.md) | Running a proved plan on an engine, its SQL, routes, classes and profiles | |
| [how-to-export.md](how-to-export.md) | Exporting a contract to Substrait and ODCS | |
| [how-to-production.md](how-to-production.md) | Reproducible sinks, engine settings and versions, sharding, testing with pytest | |
| [how-to-install.md](how-to-install.md) | The extras, the wheels and the nightly builds | |
| [examples.md](examples.md) | Moved: a list of links to the steps of getting-started.md | |

## Reference

| Page | Job | Site |
|---|---|---|
| [The API reference](https://alexandernenninger.github.io/substrait-lean/reference/) | Every public function and class, from the docstrings | Reference |
| [reference-semantics.md](reference-semantics.md) | What a plan means, row by row: the open choices, every option's value, the Ibis frontend and how the model holds a plan | Semantics |
| [stability.md](stability.md) | What 1.x keeps: the formats, the proofs, the API, the engines | Semantics |
| [upgrading-0.9.md](upgrading-0.9.md) | Upgrading from 0.8 to 0.9: a migration note with an example for each breaking change, and the evidence of each soundness fix | |
| [realizability.md](realizability.md) | Each engine's class on every option, generated | Ledgers |
| The ledgers | Upstream bugs, spec gaps, engine facts, the checklist's coverage | Ledgers |

## Explanation

| Page | Job | Site |
|---|---|---|
| [core-and-profiles.md](core-and-profiles.md) | The core, an abstract machine, and the profiles that narrow it: the reference, each engine's, Substrait's | Design |
| [what-sverify-proves.md](what-sverify-proves.md) | What the checker proves, the reference semantics and the engines, in a page | Design |
| [verifying.md](verifying.md) | Verifying under the reference or under an engine's profile, the routes each takes, and what the report says | Design |
| [report.md](report.md) | What a report holds, and how a verdict traces to what supports it | Design |
| [rejections.md](rejections.md) | Where the reference raises, the precondition that rules each case out, and how to read a refusal | Design |
| [engines.md](engines.md) | The engines, how to choose one, and what to install | Design |
| [how-it-works.md](how-it-works.md) | The checker, incremental views, the producers | Design |
| [proved-theorems.md](proved-theorems.md) | The theorems behind each guarantee, by their Lean names: contracts, composition, runtime errors, incremental views, table formats | |
| [theorems/README.md](theorems/README.md) | One page per top-level theorem: what it says, what it assumes, the Lean statement line by line, an example | |
| [engine-profiles.md](engine-profiles.md) | Each engine's profile, shims and translation | Design |
| [float-bounds.md](float-bounds.md) | Error bounds for doubles and their proofs | Design |
| [refresh-findings.md](refresh-findings.md) | What the refresh protocol's model found, and what is proved of it | Design |
| [optimizations.md](optimizations.md) | Proved optimizations and incremental maintenance | Design |
| [nested-values.md](nested-values.md) | Lists, structs and lambdas in the model | Design |
| [trusted-base.md](trusted-base.md) | What a result rests on: the kernel-checked theorems, what tests cover, what is trusted | Design |
| [how-this-is-built.md](how-this-is-built.md) | Who writes and checks the project, what to check without trusting anyone, how to disagree | |
| [comparison.md](comparison.md) | Sverify beside dbt tests, Great Expectations, Soda and data contracts, by bug class | Design |
| [prior-work.md](prior-work.md) | The work sverify builds on, and related tools | Design |

## For contributors

| Page | Job |
|---|---|
| [core-semantics.md](core-semantics.md) | The design of the loose core: how profiles state their constraints, the value domain, translations and their soundness |
| [decisions.md](decisions.md) | The decision log: each choice of the reference, the core and the profiles, with when and why |
| [ledger.md](ledger.md) | Every project decision in one list, by scope, with who decided and what is in force, generated from [`decisions/`](../decisions/) |
| [proofs.md](proofs.md) | Each guarantee with its theorem, what is trusted, one line per Lean module |
| [coverage-targets.md](coverage-targets.md) | The constructs 1.0 covers, by area, with where each stands |
| [coverage.md](coverage.md) | The Ibis operations that reach the checker and the engines that run their plans, generated on `main` |
| [layers.md](layers.md) | The layers of the Python package |
| [teaching.md](teaching.md) | How each feature is taught: its sentence, first contact, notebook and theorem; every refusal with its exit |
| [build-performance.md](build-performance.md) | The Lean build's time and memory per module, how they are measured, and the budget CI checks |
| [dbt-measurements.md](dbt-measurements.md) | sverify-dbt on jaffle_shop and Cal-ITP's warehouse: models read, tests proved, test queries skipped |
| [release-notes-1.0.0rc1.md](release-notes-1.0.0rc1.md) | A draft of 1.0.0rc1's notes: what an upgrade from 0.8.0 changes, from the changelog fragments |

## Where each topic lives

| Topic | Home |
|---|---|
| Which engines sverify supports | [stability.md, Engines](stability.md#engines) |
| What refresh maintains incrementally | [how-to-nodes.md, Nodes](how-to-nodes.md#nodes-composing-storing-refreshing) |
| Routes and classes, for users | [how-to-engines-and-sql.md, Routes, classes and profiles](how-to-engines-and-sql.md#routes-classes-and-profiles) |
| What a plan means | [reference-semantics.md](reference-semantics.md) |
| What an Ibis expression means | [reference-semantics.md, The Ibis frontend](reference-semantics.md#the-ibis-frontend) |
| How engine facts are judged | [characterization/README.md](../characterization/README.md) |
| Each engine's translation and shims | [engine-profiles.md](engine-profiles.md) |
| Each option's value | [reference-semantics.md, Options](reference-semantics.md#options) |
| Profiles, for users | [core-and-profiles.md](core-and-profiles.md) |
| Profile tables, translations, soundness | [core-semantics.md](core-semantics.md) |
| Why each choice was made | [decisions.md](decisions.md) |
| What is decided, by whom, and what replaced it | [ledger.md](ledger.md) |
| What is proved | [proofs.md](proofs.md), [proved-theorems.md](proved-theorems.md) |
| What is trusted | [trusted-base.md](trusted-base.md) |
| The Lean build's time and memory, and its budget | [build-performance.md](build-performance.md) |
| How each feature is taught, and each refusal's exit | [teaching.md](teaching.md) |
| Float error bounds | [float-bounds.md](float-bounds.md) |
| The refresh protocol: what the model found, and what is proved | [refresh-findings.md](refresh-findings.md) |
| Credits | [prior-work.md](prior-work.md) |
| Install | [python/README.md](../python/README.md) |
| The formats sverify writes | [stability.md, The formats](stability.md#the-formats) |
| What each directory holds | [README.md, How the parts fit](../README.md#how-the-parts-fit) |
