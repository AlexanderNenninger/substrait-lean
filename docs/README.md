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
and every notebook once.

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

The notebooks run on molab from the `published` branch, which follows the
release on PyPI.

## How-to

| Page | Job | Site |
|---|---|---|
| [tasks.md](tasks.md) | One section per task: contracts, runtime errors and guards, inferred bounds, the command line, nodes and refresh, quarantine, Delta and Iceberg, credentials, OpenLineage, engines and SQL, routes, export, ODCS, pytest | |
| [examples.md](examples.md) | Moved: a list of links to the steps of getting-started.md | |
| [guide.md](guide.md) | Moved: each section links to its home in getting-started.md or tasks.md | |

## Reference

| Page | Job | Site |
|---|---|---|
| [The API reference](https://alexandernenninger.github.io/substrait-lean/reference/) | Every public function and class, from the docstrings | Reference |
| [reference-semantics.md](reference-semantics.md) | What a plan means, row by row: the open choices, every option's value, the Ibis frontend and how the model holds a plan | Semantics |
| [stability.md](stability.md) | What 1.x keeps: the formats, the proofs, the API, the engines | Semantics |
| [realizability.md](realizability.md) | Each engine's class on every option, generated | Ledgers |
| The ledgers | Upstream bugs, spec gaps, engine facts, the checklist's coverage | Ledgers |

## Explanation

| Page | Job | Site |
|---|---|---|
| [core-and-profiles.md](core-and-profiles.md) | The core, an abstract machine, and the profiles that narrow it: the reference, each engine's, Substrait's | Design |
| [verifying.md](verifying.md) | Verifying under the reference or under an engine's profile, the routes each takes, and what the report says | Design |
| [how-it-works.md](how-it-works.md) | The checker, incremental views, the producers, what is proved | Design |
| [engine-profiles.md](engine-profiles.md) | Each engine's profile, shims and translation | Design |
| [float-bounds.md](float-bounds.md) | Error bounds for doubles and their proofs | Design |
| [optimizations.md](optimizations.md) | Proved optimizations and incremental maintenance | Design |
| [nested-values.md](nested-values.md) | Lists, structs and lambdas in the model | Design |
| [trusted-base.md](trusted-base.md) | What a result rests on: the kernel-checked theorems, what tests cover, what is trusted | Design |
| [prior-work.md](prior-work.md) | The work sverify builds on, and related tools | Design |

## For contributors

| Page | Job |
|---|---|
| [core-semantics.md](core-semantics.md) | The design of the loose core: how profiles state their constraints, the value domain, translations and their soundness |
| [decisions.md](decisions.md) | The decision log: each choice of the reference, the core and the profiles, with when and why |
| [proofs.md](proofs.md) | Each guarantee with its theorem, what is trusted, one line per Lean module |
| [coverage-targets.md](coverage-targets.md) | The constructs 1.0 covers, by area, with where each stands |
| [layers.md](layers.md) | The layers of the Python package |
| [teaching.md](teaching.md) | How each feature is taught: its sentence, first contact, notebook and theorem; every refusal with its exit |
| [build-performance.md](build-performance.md) | The Lean build's time and memory per module, how they are measured, and the budget CI checks |

## Where each topic lives

| Topic | Home |
|---|---|
| Which engines sverify supports | [stability.md, Engines](stability.md#engines) |
| What refresh maintains incrementally | [tasks.md, Nodes](tasks.md#nodes-composing-storing-refreshing) |
| Routes and classes, for users | [tasks.md, Routes, classes and profiles](tasks.md#routes-classes-and-profiles) |
| What a plan means | [reference-semantics.md](reference-semantics.md) |
| What an Ibis expression means | [reference-semantics.md, The Ibis frontend](reference-semantics.md#the-ibis-frontend) |
| How engine facts are judged | [characterization/README.md](../characterization/README.md) |
| Each engine's translation and shims | [engine-profiles.md](engine-profiles.md) |
| Each option's value | [reference-semantics.md, Options](reference-semantics.md#options) |
| Profiles, for users | [core-and-profiles.md](core-and-profiles.md) |
| Profile tables, translations, soundness | [core-semantics.md](core-semantics.md) |
| Why each choice was made | [decisions.md](decisions.md) |
| What is proved | [proofs.md](proofs.md) |
| What is trusted | [trusted-base.md](trusted-base.md) |
| The Lean build's time and memory, and its budget | [build-performance.md](build-performance.md) |
| How each feature is taught, and each refusal's exit | [teaching.md](teaching.md) |
| Float error bounds | [float-bounds.md](float-bounds.md) |
| The refresh protocol, model-checked | [models/refresh/README.md](../models/refresh/README.md) |
| Credits | [prior-work.md](prior-work.md) |
| Install | [python/README.md](../python/README.md) |
| The formats sverify writes | [stability.md, The formats](stability.md#the-formats) |
| What each directory holds | [README.md, How the parts fit](../README.md#how-the-parts-fit) |
