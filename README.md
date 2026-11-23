# Substrait-Lean

A formal model of [Substrait](https://substrait.io) relational plans in
[Lean 4](https://lean-lang.org), and `sverify`, a Python package built on it.
Sverify proves a data pipeline's contracts before it runs, gets the same
result on DuckDB, Polars and Spark up to the plan's stated tolerance, and keeps
it up to date from Delta Lake and Iceberg change feeds. Sverify proves the
agreement against a model of each engine's scalar functions, from the
checker's own report (`check_proved_on`): for a plan without open measures
(`closed`), on DuckDB a guard-free report without issues under the reference,
on Polars and Spark a guard-free one. That the models match the engines
rests on tests ([what is proved](docs/proved-theorems.md), [what is trusted](docs/trusted-base.md)). [How this project is built](docs/how-this-is-built.md) says who writes it and what you can check yourself. This README is for people working on the
project. Users start at [python/README.md](python/README.md), which is also
sverify's PyPI page.

We aim to make sverify an assistant that makes data engineering more joyful:
fewer 3 a.m. pages over an unexpected NULL, fewer afternoons spent finding out
why two engines disagree, and more trust in the tables you hand to the next
team.

Sverify is a working prototype of a pipeline tool: it proves contracts and runs the checked plan. Production shouldn't depend on it yet, as the API will change (sometimes drastically) between minor releases. It describes each engine as observed at pinned versions, without certifying or ranking it, and isn't affiliated with any engine's project or vendor.

## Principles

Sverify's Lean core does a superset of operations, and profiles refine it:
the reference, Substrait's and one per engine
([core, profiles and engines](docs/core-semantics.md#core-profiles-and-engines)). Sverify checks every plan against
the reference profile, and describes each engine by how it differs from
that reference. Four principles
decide what the reference does: it follows Substrait, takes the least
surprising choice where Substrait is silent, can be followed by every engine
with reasonable effort, and keeps optimizations provable. They are stated,
with what each means in practice, in
[reference-semantics.md](docs/reference-semantics.md#principles).

Engine quirks belong in the engine profiles ([engine-profiles.md](docs/engine-profiles.md)).
Changing the reference is a breaking change.

Sverify builds on a lot of prior work, from Substrait, Lean and DuckDB to research on SQL semantics, incremental views and floating point. [prior-work.md](docs/prior-work.md) credits it and places sverify next to related tools.

## How the parts fit

```text
Ibis expression ─► vendored Ibis producer ─┐
                                           ├─► Substrait plan ─► substrait-check (Lean) ─► checked plan, contract
SQL string ─► SQLGlot lift ────────────────┘                                              report, delta plans
                                                                                           │
                                           DuckDB · Polars · Spark · Snowflake SQL ◄───────┘
```

* Lean (`SubstraitLean/`, `Main.lean`) defines what a plan means
  (`Rel.eval`), and proves what sverify relies on: contracts, runtime-error
  analysis, incremental delta plans, sharding and rewrites. It builds the
  `substrait-check` command line tool, which reads a Substrait JSON plan and
  prints what it proved.
* Python (`python/`) is the `sverify` package. It produces plans from Ibis
  and SQL, calls `substrait-check`, writes the checked plan for each engine,
  and runs it. Delta and Iceberg IO, nodes, sinks and the pytest plugin live
  there too.
* The two meet at one interface: Substrait JSON in, a report and rewritten
  plans out. Lean's parser, the writers that print each engine's SQL or code and the
  lowerings of Polars and Spark are trusted code; golden and differential tests
  cover them. The generated DuckDB lowering table is proved exact against the
  model of DuckDB (`Lowering.duckdb_exact`), and the model's match to the real
  engine rests on tests ([trusted base](docs/trusted-base.md)).

| Directory | Contents |
|---|---|
| `core/` | The Lean core, `Sverify.Core`: values, expressions, `Rel.eval` and the options; it imports only Lean |
| `analysis/` | `Sverify.Analysis`: what the checker proves of a plan under the core, with no engine in it |
| `engines/` | `Sverify.Engines`, what every engine shares in Lean; and one directory per engine package (`polars/`, `spark/`), each a Python distribution with its plugin, facts and probes |
| `SubstraitLean/`, `Main.lean` | The profiles, lowerings and lifts, the checker's modes and the `substrait-check` CLI ([the files](#the-lean-project)) |
| `python/src/sverify/` | The package: `contracts`, `nodes`, `incremental`, `io/`, `sql/` (SQL per dialect), `sql_lift`, `ibis_substrait/` (vendored producer), `profiles` (the engine plugins), `duckdb_engine.py`, `testing`, `pytest_plugin` |
| `python/tools/sverify_dev/` | Development tools: the Ibis coverage harness, the catalogue runner, fuzzers, the sqllogictest replay |
| `python/tests/` | The Python tests: differential tests against `Rel.eval`, golden SQL snapshots, README examples |
| `tests/` | Golden tests of the CLI (`tests/run.sh`, plans in `tests/fixtures`) and lowering expectations |
| `notebooks/` | The tour, in [marimo](https://marimo.io) ([below](#the-tour)) |
| `catalogue/` | 139 real analytical queries (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O and more), probed against the checker and the engines; [findings](catalogue/FINDINGS.md) |
| `characterization/` | How engine facts are judged: the areas, the fact schema and the oracle-A baseline. The facts are in `engines/<engine>/facts/`: one JSON document per fact, a diff against the reference profile, with provenance ([DuckDB's facts](engines/duckdb/facts/)) |
| `dbt/` | `sverify-dbt`, which checks a dbt project's tests and contracts ([dbt/README.md](dbt/README.md)) |
| `models/` | The refresh protocol, model-checked in TLA+ |
| `templates/` | A template repository for pipelines ([templates/pipelines/README.md](templates/pipelines/README.md)) |
| `docs/` | The documents below |
| `float-bounds/` | A separate Lean package of error bounds for doubles |
| `upstream/` | Bugs found in SQLGlot, engines, Ibis and Substrait tooling, to file upstream: one JSON document per bug ([the bugs](upstream/bugs/)), and [a report](upstream/REPORT.md) of what is filed, fixed and still to report, with the counts per project |
| `changelog.d/` | One fragment per user-visible change; the release folds them into `CHANGELOG.md` |

## Documents

[docs/README.md](docs/README.md) maps every page by its kind: the tutorial
([docs/getting-started.md](docs/getting-started.md), ten steps from a first
contract to Substrait's own semantics), the how-to pages
([docs/tasks.md](docs/tasks.md), one page per task), the reference
([docs/reference-semantics.md](docs/reference-semantics.md),
[docs/stability.md](docs/stability.md), which says what stays stable in 1.x
and [which engines](docs/stability.md#engines) sverify supports), the
explanations ([docs/how-it-works.md](docs/how-it-works.md),
[docs/what-sverify-proves.md](docs/what-sverify-proves.md),
[docs/prior-work.md](docs/prior-work.md)) and the pages for contributors
([docs/core-semantics.md](docs/core-semantics.md),
[docs/proofs.md](docs/proofs.md),
[docs/coverage-targets.md](docs/coverage-targets.md),
[docs/layers.md](docs/layers.md)).
[python/README.md](python/README.md) is the user's entry. How engine facts
are judged is in [characterization/README.md](characterization/README.md), and
the refresh protocol, model-checked in TLA+, in [models/refresh/](models/refresh/README.md).

## The Lean project

`lake build` checks every proof and builds `substrait-check`. The project has
no dependencies beyond Lean itself, and is four Lake packages: the core
(`core/`), the analysis (`analysis/`), what the engines share (`engines/`) and
the root (`SubstraitLean/`), which holds the profiles, lowerings and the CLI. A
cold build takes about four minutes on 12 threads, a no-op build a second
([build-performance.md](docs/build-performance.md)). The plan model (`Rel`,
`Expr`, `Value`) comes first, then the checkers built on it (contracts,
runtime errors, delta plans, sharding), then the parser and writer, which are
trusted code.

[docs/proofs.md](docs/proofs.md) maps every Lean module to its job and
names the theorems each guarantee rests on. The rest of the repository:

| File | Contents |
|---|---|
| `python/` | `sverify`: contracts, incremental views, pipelines, Delta/Iceberg IO, sharding; the DuckDB runner and the Snowflake SQL ([the engines](docs/stability.md#engines)); differential tests |
| `engines/polars/`, `engines/spark/` | `sverify-polars` and `sverify-spark`, the Polars and Spark engines as packages of their own |
| `notebooks/` | The tour: three workflows and three guides (marimo) |
| `tests/` | Golden tests of the CLI (`tests/run.sh`, plans in `tests/fixtures`) |
| `docs/optimizations.md` | Proved optimizations beyond incremental maintenance: what engines already do, what is proved, what is next |
| `catalogue/` | 139 real analytical queries (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O, practitioner, IoT and finance idioms), probed against the checker and the engines; [`FINDINGS.md`](catalogue/FINDINGS.md) |

## Ibis coverage

[docs/coverage.md](docs/coverage.md) has the table of the Ibis operations that
reach the checker and the engines that run their plans, which the
`Generated files` workflow rewrites on `main` after every merge.

## Development

To work on the project or run the tour from a clone, you need [uv](https://docs.astral.sh/uv/) for Python,
[elan](https://github.com/leanprover/elan) for Lean (elan is to Lean what
rustup is to Rust, or uv to Python), and Java 17 or 21 for the Spark tests:

```bash
# skip: installs software on the reader's machine
brew install uv          # or: curl -LsSf https://astral.sh/uv/install.sh | sh
```
```bash
# skip: installs software on the reader's machine
brew install openjdk@21  # or: sudo apt install openjdk-21-jre-headless
```

Homebrew's JDK is not on the `PATH`; point `JAVA_HOME` at it (in `~/.zshrc`):

```bash
# skip: sets the reader's JAVA_HOME
export JAVA_HOME=/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home
```

Without a JVM the Spark tests are skipped and everything else runs.
```bash
# skip: installs software on the reader's machine
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Open a new terminal so `lake` (Lean's build tool) is on your PATH, then run, from
the project root:

```bash
# skip: builds or tests the repository, which needs elan and takes minutes
lake build                       # checks every proof and builds the substrait-check CLI
```
```bash
# skip: builds or tests the repository, which needs elan and takes minutes
cd python && uv sync             # sverify with every extra, and the dev tools (pytest, hypothesis, …)
```
```bash
# skip: builds or tests the repository, which needs elan and takes minutes
uv run pytest                    # all pass; the Spark tests skip without a JVM
```

`uv sync` installs `sverify` in editable mode, with every extra (below). Its build hook runs
`lake build substrait-check` and links `sverify/_bin/substrait-check` to the
result, so later `lake build`s take effect without reinstalling. To use a
different binary, set `SVERIFY_CHECKER` to its path.

### Development tasks

Tasks are defined with [poe](https://poethepoet.natn.io) in `python/pyproject.toml`:

```bash
# skip: builds or tests the repository, which needs elan and takes minutes
cd python && uv run poe qa       # everything below, in order; stops at the first failure
```

| Task | What it does |
|---|---|
| `poe prove` | Checks every Lean proof. Any warning fails, including a `sorry` (an unfinished proof). |
| `poe build` | Builds the `substrait-check` CLI that `sverify` calls |
| `poe lint` | `ruff check` and `ruff format --check`, on `python/` and `notebooks/` |
| `poe fmt` | Fixes lint issues and formats the Python code |
| `poe typecheck` | Type-checks the Python code with pyrefly |
| `poe golden` | Golden tests: CLI output on every plan in `tests/fixtures` |
| `poe test` | The fast Python tests on 2 workers: no `slow` tests, a tenth of the Hypothesis examples (see `python/tests/conftest.py`) |
| `poe test-all` | Every Python test with the full Hypothesis counts, on every core, as `qa` and CI run them |
| `poe test-core`, `test-duckdb`, `test-polars`, `test-snowflake`, `test-spark` | The Python tests of one backend (`pytest -m <backend>`). CI runs one job per backend, three for `core`. |
| `poe notebooks` | Checks the tour notebooks and runs each one headless |
| `poe docs`, `poe docs_preview` | Builds the API reference site into `python/great-docs/_site` (or serves it locally), with the examples and the ledgers, which `poe docs_pages` writes from `docs/examples.md` and the JSON first. Needs [Quarto](https://quarto.org) and `uv sync --group docs`; not part of `qa` |

From the project root, use `uv run --project python poe -C python qa`. The Lean
tasks need `lake` on your PATH.

### The tour

The eight notebooks in [`notebooks/`](notebooks) form a guided tour, starting at
[`01_duplicate_payments.py`](notebooks/01_duplicate_payments.py). Open the whole folder, so the
links between notebooks work:

```bash
# skip: opens an editor server
uvx marimo edit --sandbox notebooks              # from the project root
```
```bash
# skip: opens a server
uvx marimo run --sandbox --include-code notebooks   # read-only apps
```

`--sandbox` runs each notebook in its own environment, with `sverify` installed
from `python/` as declared in the notebook's header; the first start takes a
minute. Build the checker first (`lake build`). The project's own
environment works too: `uv run --project python marimo edit notebooks`.

| | Notebook | What it covers |
|---:|:---|:---|
| 1 | [Duplicate card payments](notebooks/01_duplicate_payments.py) | workflow: Delta source and sink, a self-join's contract, refresh from the Change Data Feed |
| 2 | [Sensor alerts](notebooks/02_sensor_alerts.py) | workflow: Iceberg source and sink, `LAG` and ties, NaN, Snowflake and Spark |
| 3 | [An orders mart](notebooks/03_orders_mart.py) | workflow: a point-in-time join to a type-2 dimension, dbt tests as a contract, SQL |
| 4 | [Contracts](notebooks/04_contracts.py) | `requires`/`ensures`, keys and relations, runtime errors, windows and ASOF joins, composing contracts |
| 5 | [Pipelines and engines](notebooks/05_pipelines_and_engines.py) | incremental views, nodes and sinks, DuckDB, Polars, Spark and Snowflake SQL, doubles, time and text |
| 6 | [Running it in production](notebooks/06_running_in_production.py) | `sverify check --diff` and `--fix`, a pytest test, credentials by name, OpenLineage, late rows and bounded state |
| 7 | [Engines](notebooks/07_engines.py) | one proved plan on DuckDB, Polars and Spark, the routes that carry the proof, SQL for Spark and Snowflake, refusals and their exits |
| 8 | [Your dbt project](notebooks/08_dbt.py) | `sverify_dbt.check`, the tests proved before the models run, a counterexample and its fix, `--selectors`, refusals and their exits |

[catalogue/backend_semantics.py](catalogue/backend_semantics.py) is a marimo app outside the tour: one
expression asked of every engine. Under-the-hood detail is in
[docs/how-it-works.md](docs/how-it-works.md).

`poe notebooks` (part of `poe qa`) checks every notebook with `marimo check` and
runs it headless. The notebooks' tables come from `sverify.display`, which needs
marimo.

### Wheels

`uv build python --wheel` builds a wheel for the current platform. It bundles a
stripped `substrait-check`, so installing it needs neither Lean nor elan. The
[Wheels workflow](.github/workflows/wheels.yml) builds and tests wheels for Linux
(x86_64, aarch64) and macOS (arm64). A `v*` tag that matches the
version in `python/pyproject.toml` also publishes them to PyPI. Each night,
when `main` has changed, it publishes them as the
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly)
([python/README.md](python/README.md) shows how to install them). Start one by
hand on `main` with `gh workflow run wheels.yml -f nightly=nightly`.

`uv build python` also builds the sdist. It carries the Lean project under
`lean/`, and `uv build` makes the wheel from it, so the sdist is checked on
every build. Installing from the sdist (on a platform without a wheel) needs
elan; the build hook runs `lake build` there.

To run your own scripts with the package available, from the project root:

```bash
# skip: runs the reader's pipeline
uv run --project python python my_pipeline.py
```

### Troubleshooting

* `lake: command not found`: open a new terminal, or call `~/.elan/bin/lake`.
* `no configuration file …lakefile`: run `lake` from the project root, where `lakefile.lean` is.
* `… does not exist` for a notebook or `--project` path: those paths are relative to the
  project root, and `python/` is not the root.

## Open work

Open work is in the
[issue tracker](https://github.com/AlexanderNenninger/substrait-lean/issues);
the [roadmap to 1.0](https://github.com/AlexanderNenninger/substrait-lean/issues/757)
lists what 1.0 needs.

## License

Sverify is licensed under the [Mozilla Public License 2.0](LICENSE) (MPL-2.0).
You can use it in any product, open or proprietary, and your own code stays
yours. If you distribute a modified version of sverify's own files, those
files stay under the MPL and you share their source. The license applies file
by file, so it never reaches the code around them.

`python/src/sverify/ibis_substrait/` is derived from
[ibis-substrait](https://github.com/ibis-project/ibis-substrait) and stays
under the [Apache License 2.0](python/src/sverify/ibis_substrait/LICENSE).
