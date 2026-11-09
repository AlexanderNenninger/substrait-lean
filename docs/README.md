# A map of the docs

Every page of sverify's docs is one of four kinds, and each kind has one job
([#751](https://github.com/AlexanderNenninger/substrait-lean/issues/751)):

- a tutorial teaches by doing, start to finish;
- a how-to guide solves one task;
- a reference states the facts, to look up;
- an explanation says how and why.

Each topic has one home, and the other pages link to it
([#1016](https://github.com/AlexanderNenninger/substrait-lean/issues/1016)).
The [docs site](https://alexandernenninger.github.io/substrait-lean/) renders
the pages marked "site", in the section named; the rest are read here.
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
| [notebooks/01_duplicate_payments.py](../notebooks/01_duplicate_payments.py) | A Delta pipeline that catches double charges |
| [notebooks/02_sensor_alerts.py](../notebooks/02_sensor_alerts.py) | An Iceberg pipeline of sensor alerts: ties, NaN, windows |
| [notebooks/03_orders_mart.py](../notebooks/03_orders_mart.py) | An orders mart: a point-in-time join, dbt's tests as a contract |
| [notebooks/04_contracts.py](../notebooks/04_contracts.py) | Contracts in depth: keys, relations, runtime errors, composition |
| [notebooks/05_pipelines_and_engines.py](../notebooks/05_pipelines_and_engines.py) | Pipelines and engines: delta rules, quarantine, routes, doubles |
| [notebooks/06_running_in_production.py](../notebooks/06_running_in_production.py) | Running it in production: the command in CI, tests, credentials, lineage, late rows |

The notebooks run on molab from the `published` branch (CLAUDE.md,
"Notebooks on molab").

## How-to

| Page | Job | Site |
|---|---|---|
| [guide.md](guide.md) | Every task, one section each: contracts, runtime errors and guards, inferred bounds, the command line, nodes and refresh, quarantine, Delta and Iceberg, credentials, OpenLineage, engines and SQL, routes, export, ODCS, pytest ([#753](https://github.com/AlexanderNenninger/substrait-lean/issues/753) splits it) | |
| [examples.md](examples.md) | Ten short examples, each a step up | Examples |

## Reference

| Page | Job | Site |
|---|---|---|
| [The API reference](https://alexandernenninger.github.io/substrait-lean/reference/) | Every public function and class, from the docstrings | Reference |
| [reference-semantics.md](reference-semantics.md) | What a plan means, row by row, the Ibis frontend and how the model holds a plan | Semantics |
| [stability.md](stability.md) | What 1.x keeps: the formats, the proofs, the API, the engines | Semantics |
| [coverage-targets.md](coverage-targets.md) | The constructs 1.0 covers, by area | Semantics |
| [realizability.md](realizability.md) | Each engine's class on every option, generated | Ledgers |
| [teaching.md](teaching.md) | How each feature is taught: its sentence, first contact, notebook and theorem; every refusal with its exit | |
| The ledgers | Upstream bugs, spec gaps, engine facts, the checklist's coverage | Ledgers |

## Explanation

| Page | Job | Site |
|---|---|---|
| [how-it-works.md](how-it-works.md) | The checker, incremental views, the producers, what is proved | Design |
| [core-semantics.md](core-semantics.md) | The loose core, which does a superset of operations, the profiles that refine it, translations, the decisions D1 onwards | Design |
| [engine-profiles.md](engine-profiles.md) | Each engine's profile, shims and translation | Design |
| [float-bounds.md](float-bounds.md) | Error bounds for doubles and their proofs | Design |
| [optimizations.md](optimizations.md) | Proved optimizations and incremental maintenance | Design |
| [nested-values.md](nested-values.md) | Lists, structs and lambdas in the model | Design |
| [proofs.md](proofs.md) | Each guarantee with its theorem, what is trusted, one line per module | Design |
| [trusted-base.md](trusted-base.md) | What a result rests on: the kernel-checked theorems, what tests cover, what is trusted | Design |
| [layers.md](layers.md) | The layers of the Python package | Design |
| [prior-work.md](prior-work.md) | The work sverify builds on, and related tools | Design |

## Where each topic lives

| Topic | Home |
|---|---|
| Which engines sverify supports | [stability.md, Engines](stability.md#engines) |
| What refresh maintains incrementally | [guide.md, Nodes](guide.md#nodes-composing-storing-refreshing) |
| Routes and classes, for users | [guide.md, Routes, classes and profiles](guide.md#routes-classes-and-profiles) |
| What a plan means | [reference-semantics.md](reference-semantics.md) |
| What an Ibis expression means | [reference-semantics.md, The Ibis frontend](reference-semantics.md#the-ibis-frontend) |
| How engine facts are judged | [characterization/README.md](../characterization/README.md) |
| Each engine's translation and shims | [engine-profiles.md](engine-profiles.md) |
| Profiles, options, soundness, decisions | [core-semantics.md](core-semantics.md) |
| What is proved | [proofs.md](proofs.md) |
| What is trusted | [trusted-base.md](trusted-base.md) |
| How each feature is taught, and each refusal's exit | [teaching.md](teaching.md) |
| Float error bounds | [float-bounds.md](float-bounds.md) |
| The refresh protocol, model-checked | [models/refresh/README.md](../models/refresh/README.md) |
| Credits | [prior-work.md](prior-work.md) |
| Install | [python/README.md](../python/README.md) |
| The formats sverify writes | [stability.md, The formats](stability.md#the-formats) |
| What each directory holds | [README.md, How the parts fit](../README.md#how-the-parts-fit) |
