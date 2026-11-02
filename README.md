# Substrait-Lean

A formal model of [Substrait](https://substrait.io) relational plans in
[Lean 4](https://lean-lang.org), and `sverify`, a Python package built on it.
Sverify proves a data pipeline's contracts before it runs, gets the same
result on DuckDB, Polars, DataFusion and Spark, and keeps it up to date from
Delta Lake and Iceberg change feeds ([what is proved](docs/how-it-works.md#what-is-proved)). This README is for people working on the
project. Users start at [python/README.md](python/README.md), which is also
sverify's PyPI page.

We aim to make sverify an assistant that makes data engineering more joyful:
fewer 3 a.m. pages over an unexpected NULL, fewer afternoons spent finding out
why two engines disagree, and more trust in the tables you hand to the next
team.

Sverify is purely observational. It's a tool to explore and compare database semantics. Although it is already quite useful, production shouldn't depend on it yet, as the API will change (sometimes drastically) between minor releases. It describes each engine as observed at pinned versions, without certifying or ranking it, and isn't affiliated with any engine's project or vendor.

## How the parts fit

```text
Ibis expression ─► vendored Ibis producer ─┐
                                           ├─► Substrait plan ─► substrait-check (Lean) ─► checked plan, contract
SQL string ─► SQLGlot lift ────────────────┘                                              report, delta plans
                                                                                           │
                              DuckDB · Polars · DataFusion · Spark · Snowflake SQL ◄───────┘
```

* Lean (`SubstraitLean/`, `Main.lean`) defines what a plan means
  (`Rel.eval`), and proves what sverify relies on: contracts, runtime-error
  analysis, incremental delta plans, sharding and rewrites. It builds the
  `substrait-check` command line tool, which reads a Substrait JSON plan and
  prints what it verified.
* Python (`python/`) is the `sverify` package. It produces plans from Ibis
  and SQL, calls `substrait-check`, writes the checked plan for each engine,
  and runs it. Delta and Iceberg IO, nodes, sinks and the pytest plugin live
  there too.
* The two meet at one interface: Substrait JSON in, a report and rewritten
  plans out. Lean's parser and writer and the engine lowerings are trusted
  code; golden and differential tests cover them.

| Directory | Contents |
|---|---|
| `SubstraitLean/`, `Main.lean` | The Lean library and the `substrait-check` CLI ([the files](#the-lean-project)) |
| `python/src/sverify/` | The package: `contracts`, `nodes`, `incremental`, `io/`, `sql/` (SQL per engine), `sql_lift`, `ibis_substrait/` (vendored producer), `*_engine.py`, `testing`, `pytest_plugin` |
| `python/tools/sverify_dev/` | Development tools: the Ibis coverage harness, the catalogue runner, fuzzers, the sqllogictest replay |
| `python/tests/` | The Python tests: differential tests against `Rel.eval`, golden SQL snapshots, README examples |
| `tests/` | Golden tests of the CLI (`tests/run.sh`, plans in `tests/fixtures`) and lowering expectations |
| `notebooks/` | The tour, in [marimo](https://marimo.io) ([below](#the-tour)) |
| `catalogue/` | 139 real analytical queries (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O and more), probed against the checker and the engines; [findings](catalogue/FINDINGS.md) |
| `characterization/duckdb/` | DuckDB's behaviour as a diff against the reference model ([facts](characterization/duckdb/FACTS.md)) |
| `docs/` | The documents below |
| `float-bounds/` | A separate Lean package of error bounds for doubles |
| `upstream/LEDGER.md` | Bugs found in SQLGlot, engines, Ibis and Substrait tooling, to file upstream |
| `changelog.d/` | One fragment per user-visible change; the release folds them into `CHANGELOG.md` |

## Documents

* [docs/guide.md](docs/guide.md): what sverify does and how to use it,
  from contracts to Delta and Iceberg pipelines.
* [docs/how-it-works.md](docs/how-it-works.md): the checker, incremental
  maintenance, the producers and engines, what is proved and what is trusted.
* [docs/reference-semantics.md](docs/reference-semantics.md): what `Rel.eval`
  means, row by row; [docs/ibis-semantics.md](docs/ibis-semantics.md),
  [docs/engine-profiles.md](docs/engine-profiles.md),
  [docs/optimizations.md](docs/optimizations.md),
  [docs/nested-values.md](docs/nested-values.md) and
  [docs/float-bounds.md](docs/float-bounds.md) cover the Ibis side, the engines,
  proved optimizations, nested values and doubles.
* [python/README.md](python/README.md): install, quick example, API overview and
  the engine tiers (DuckDB is Tier 1).

## The Lean project

`lake build` checks every proof and builds `substrait-check`. The library has
no dependencies beyond Lean core, so the build takes seconds. The plan model
(`Rel`, `Expr`, `Value`) comes first, then the checkers built on it
(contracts, runtime errors, delta plans, sharding), then the parser and
writer, which are trusted code.

| File | Contents |
|---|---|
| `SubstraitLean/Value.lean` | Nullable values, rows, bag-semantics relations |
| `SubstraitLean/Float.lean` | Doubles as exact integer codes (multiples of 2⁻¹⁰⁷⁴), NaN and −0.0 |
| `SubstraitLean/Rounding.lean` | Exact `FLOOR`/`CEIL`/`ROUND` and casts to `BIGINT` on double codes; monotonicity |
| `SubstraitLean/Text.lean` | String functions, `LIKE`; black-box `UPPER`/`LOWER`/regexes; patterns that certainly compile |
| `SubstraitLean/Numeric.lean` | `sqrt`, `exp`, logarithms and trigonometry of doubles (C's libm) with their domains; 64-bit bitwise operations and shifts |
| `SubstraitLean/Time.lean` | Exact `date_part` and `date_trunc` on the proleptic Gregorian calendar; monotonicity |
| `SubstraitLean/Expr.lean` | `Literal`, `FieldReference`, scalar functions, `IfThen`, Kleene 3-valued logic |
| `SubstraitLean/Window.lean` | Sort orders, `ROW_NUMBER`/`LAG`/`LEAD` semantics over partitions |
| `SubstraitLean/Aggregate.lean` | `GROUP BY` with `COUNT`/`SUM`/`MIN`/`MAX`/`AVG` (`DISTINCT`, `FILTER`) semantics |
| `SubstraitLean/Rel.lean` | `Read`, `VirtualTable`, `Filter`, `Project`, `Emit`, `Cross`, `Join` (inner/left/semi/anti), `Sort`, `Aggregate`, `Fetch`, `UnionAll`, `Window`; arity, well-formedness, `eval`; type soundness |
| `SubstraitLean/Rewrites.lean` | Verified rewrites (below) |
| `SubstraitLean/Incremental.lean` | Z-set semantics, delta rules, delta plans (incremental view maintenance) |
| `SubstraitLean/Terms.lean` | Splitting a plan into union-free terms (for DataFusion's consumer) |
| `SubstraitLean/Weighted.lean` | Weight-column encoding for bag engines; `isIncremental` |
| `SubstraitLean/Write.lean` | `Rel` → Substrait JSON, delta plans for engines (trusted) |
| `SubstraitLean/Contracts.lean` | Verified abstract interpreter: NULLs, intervals, filter refinement; `contract_sound` |
| `SubstraitLean/Keys.lean` | Derived keys (`Rel.keys_sound`), window tie-breaking (`Rel.window_deterministic`) |
| `SubstraitLean/Completeness.lean` | The converse of contracts for the IoT example: no window is lost (`IoT.window_complete`) |
| `SubstraitLean/Compose.lean` | Composing contracts (Hoare triples), preconditions under updates, views over views (chain rule) |
| `SubstraitLean/TableFormat.lean` | Change feeds (`Rel.cdf_sound`, views only depend on weights) and file statistics (`stats_table`) |
| `SubstraitLean/Safety.lean` | Runtime errors, overflow included; `Rel.mayIssues_sound` |
| `SubstraitLean/Partition.lean` | Sharded evaluation of linear plans, two-phase `COUNT`/`SUM`/`MIN`/`MAX`; `Rel.shardSplit_sound` |
| `SubstraitLean/Semantic.lean` | Rewrites from contract facts and keys (`DISTINCT` on a key, …); `Rel.optimize_sound` |
| `SubstraitLean/Guards.lean` | Guard elimination: unchecked engine functions are exact where no issue happens; `Rel.guardFree_sound` |
| `SubstraitLean/ContractCheck.lean` | `--contract`: proving postconditions from preconditions and schemas |
| `SubstraitLean/ShardCheck.lean` | `--shard`: splitting a plan into per-shard and combining plans (trusted) |
| `SubstraitLean/Check.lean` | Executable `checkWF`, proven equivalent to `Rel.WF`; `Decidable` instance |
| `SubstraitLean/Parse.lean` | Substrait protobuf-JSON → `Rel` (trusted) |
| `SubstraitLean/Pretty.lean` | Plan / row rendering |
| `Main.lean` | `substrait-check` CLI (`--delta` for engine delta plans) |
| `python/` | `sverify`: contracts, incremental views, pipelines, Delta/Iceberg IO, sharding; the DuckDB, Polars, DataFusion and Spark runners and the Snowflake SQL; differential tests |
| `notebooks/` | The tour: three workflows and two guides (marimo) |
| `tests/` | Golden tests of the CLI (`tests/run.sh`, plans in `tests/fixtures`) |
| `docs/optimizations.md` | Proved optimizations beyond incremental maintenance: what engines already do, what is proved, what is next |
| `catalogue/` | 139 real analytical queries (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O, practitioner, IoT and finance idioms), probed against the checker and the engines; [`FINDINGS.md`](catalogue/FINDINGS.md) |
| `SubstraitLean/Examples.lean` | Concrete plans checked with `#guard` at build time, plus `#print axioms` |

## Ibis coverage

How much of the Ibis API gets through, from
[`sverify_dev/coverage.py`](python/tools/sverify_dev/coverage.py) and its cases in
[`sverify_dev/coverage_cases/`](python/tools/sverify_dev/coverage_cases) (regenerated on
`main` after every merge by `uv run python -m sverify_dev.coverage --write-readme`):

<!-- coverage:start -->
171 of 204 probed Ibis operations reach the checker (✓ verified, ✗ rejected by the checker, – fails in Ibis; *inc.* marks incremental maintenance).

| Area | Operations |
|---|---|
| rows | ✓ filter, select *inc.* · ✓ mutate *inc.* · ✓ drop, rename *inc.* · ✓ drop_null *inc.* · ✓ isnull *inc.* · ✓ between *inc.* · ✓ isin *inc.* · ✓ notin *inc.* · ✓ ifelse *inc.* · ✓ cases *inc.* · ✓ order_by *inc.* · ✓ limit · ✓ limit with offset · ✓ order_by + limit · ✗ sample · ✓ order_by expression *inc.* · ✗ limit expression · ✗ limit count() · ✓ fill_null table *inc.* · ✓ fill_null all *inc.* · ✓ memtable *inc.* · ✓ constant table *inc.* · ✓ alias *inc.* · ✓ sql view *inc.* · ✓ sql query *inc.* |
| joins | ✓ inner join *inc.* · ✓ non-equi join *inc.* · ✓ cross join *inc.* · ✓ left join · ✓ right join · ✓ outer join · ✓ semi join · ✓ anti join · ✓ isin subquery · ✓ isin subquery in select · ✓ notin subquery · ✓ scalar subquery in select · ✓ scalar subquery, one row · ✗ scalar subquery, many rows · ✓ exists · ✓ not exists · ✓ exists, uncorrelated · ✗ correlated scalar subquery · ✓ union all *inc.* · ✓ union distinct · ✓ intersect · ✓ difference · ✓ intersect all · ✓ difference all |
| aggregation | ✓ count() · ✓ group_by sum · ✓ count, max, mean · ✓ arithmetic over aggregates · ✓ nunique · ✓ first, last ordered · ✓ group_concat ordered · ✗ group_concat · ✗ approx_nunique · ✓ any, all · ✓ bit_and, bit_or, bit_xor · ✓ sum(where=) · ✓ having · ✓ value_counts · ✓ distinct · ✓ distinct(on=) · ✓ std · ✓ cov, corr · ✓ collect · ✓ collect ordered · ✗ collect include_null · ✓ scalar subquery · ✓ unnest |
| lists | ✓ unnest column · ✗ unnest keep_empty · ✓ list literal *inc.* · ✓ list column *inc.* |
| windows | ✓ row_number · ✓ lag · ✓ rank · ✓ dense_rank · ✓ cumsum · ✓ sum over group · ✗ rolling mean (rows) · ✗ rolling mean (interval) · ✓ ntile · ✓ first · ✓ percent_rank, cume_dist · ✓ running mean · ✓ rolling sum (interval) · ✓ rolling sum (range) · ✓ last, nth · ✓ max, count over frame · ✗ min over a sliding frame · ✗ window sum of an expression |
| numbers | ✓ +, -, * *inc.* · ✓ float division *inc.* · ✓ integer division *inc.* · ✓ mod *inc.* · ✓ abs *inc.* · ✓ round *inc.* · ✓ ceil, floor *inc.* · ✓ power *inc.* · ✓ greatest *inc.* · ✓ least *inc.* · ✓ clip *inc.* · ✓ cast int → double *inc.* · ✓ cast int → string *inc.* · ✓ cast double → int *inc.* |
| math | ✓ sign *inc.* · ✓ sqrt *inc.* · ✓ exp *inc.* · ✓ ln *inc.* · ✓ log10, log2 *inc.* · ✓ log(base) *inc.* · ✓ trigonometry *inc.* · ✓ degrees, radians *inc.* · ✓ pi, e *inc.* · ✓ isinf *inc.* · ✓ bitwise *inc.* · ✓ shifts *inc.* · ✓ logical xor *inc.* |
| nulls | ✓ fill_null *inc.* · ✓ coalesce *inc.* · ✓ nullif *inc.* |
| strings | ✓ upper *inc.* · ✓ length *inc.* · ✓ concat *inc.* · ✓ substr *inc.* · ✓ contains *inc.* · ✓ startswith *inc.* · ✓ like *inc.* · ✓ re_search *inc.* · ✓ strip *inc.* · ✓ lpad *inc.* · ✓ rpad *inc.* · ✓ repeat *inc.* · ✓ reverse *inc.* · ✓ right *inc.* · ✓ replace *inc.* · ✓ replace '' *inc.* · ✓ ilike *inc.* · ✓ find from *inc.* · ✓ ascii *inc.* · ✓ join *inc.* · ✓ levenshtein *inc.* · ✓ find_in_set *inc.* · ✓ capitalize *inc.* · ✓ slice *inc.* · ✗ translate · ✓ re_extract *inc.* · ✓ re_replace *inc.* · ✓ hexdigest *inc.* · ✗ hash · ✗ host |
| time | ✓ timestamp + interval *inc.* · ✓ compare with literal *inc.* · ✓ year *inc.* · ✓ date *inc.* · ✓ truncate *inc.* · ✓ date + days *inc.* · ✓ date - months *inc.* · ✓ date + years *inc.* · ✓ date - column days *inc.* · ✓ timestamp + months *inc.* · ✓ constant interval arithmetic *inc.* · ✓ date - date *inc.* · ✓ date delta *inc.* · ✓ date parts *inc.* · ✓ date truncate *inc.* · ✓ day_of_week *inc.* · ✓ day_of_week name *inc.* · ✓ iso_year *inc.* · ✓ epoch_seconds *inc.* · ✓ millisecond, microsecond *inc.* · ✗ timestamp + column interval · ✗ date + column months · ✗ timestamp delta · ✓ bucket *inc.* · ✓ group_by_dynamic (no overlap) · ✓ rolling sum by time · ✓ offset_by months and days *inc.* · ✓ month end *inc.* · ✗ group_by_dynamic (overlapping) · ✓ time of day *inc.* · ✓ time parts *inc.* · ✓ compare times *inc.* · ✓ strftime *inc.* · ✓ timestamp from unix *inc.* · ✓ date from constants *inc.* · ✓ timestamp from constants *inc.* · ✗ date from columns · ✗ string to timestamp · ✗ time + interval · ✗ time truncate · ✗ strftime other directives · – between_time |
| generic | ✓ try_cast *inc.* · ✗ try_cast string · ✗ param · ✗ typeof · ✗ random · ✗ uuid · ✗ now · ✗ today |

Every engine runs the plans of the 171 verified operations, except:

| Engine | Runs | Refuses |
|---|---|---|
| Polars | 162 | non-equi join · first, last ordered · group_concat ordered · distinct(on=) · cov, corr · re_extract · re_replace · hexdigest · try_cast |
| DuckDB | 169 | non-equi join · replace '' |
| Snowflake | 126 | order_by (with `tie_free=True` it runs) · limit · limit with offset · order_by + limit · order_by expression (with `tie_free=True` it runs) · non-equi join · scalar subquery, one row · count, max, mean · first, last ordered · group_concat ordered · distinct(on=) · cov, corr · collect · collect ordered · scalar subquery · unnest · unnest column · list literal · row_number (with `tie_free=True` it runs) · lag (with `tie_free=True` it runs) · rank (with `tie_free=True` it runs) · dense_rank (with `tie_free=True` it runs) · cumsum (with `tie_free=True` it runs) · sum over group · ntile (with `tie_free=True` it runs) · first (with `tie_free=True` it runs) · percent_rank, cume_dist (with `tie_free=True` it runs) · running mean · rolling sum (interval) (with `tie_free=True` it runs) · rolling sum (range) (with `tie_free=True` it runs) · last, nth (with `tie_free=True` it runs) · max, count over frame (with `tie_free=True` it runs) · sqrt · exp · ln · log10, log2 · log(base) · trigonometry · shifts · replace '' · re_extract · re_replace · hexdigest · rolling sum by time (with `tie_free=True` it runs) · try_cast |
| Spark | 125 | order_by (with `tie_free=True` it runs) · limit · limit with offset · order_by + limit · order_by expression (with `tie_free=True` it runs) · non-equi join · scalar subquery, one row · count, max, mean · first, last ordered · group_concat ordered · distinct(on=) · cov, corr · collect · collect ordered · scalar subquery · unnest · unnest column · list literal · row_number (with `tie_free=True` it runs) · lag (with `tie_free=True` it runs) · rank (with `tie_free=True` it runs) · dense_rank (with `tie_free=True` it runs) · cumsum (with `tie_free=True` it runs) · sum over group · ntile (with `tie_free=True` it runs) · first (with `tie_free=True` it runs) · percent_rank, cume_dist (with `tie_free=True` it runs) · running mean · rolling sum (interval) (with `tie_free=True` it runs) · rolling sum (range) (with `tie_free=True` it runs) · last, nth (with `tie_free=True` it runs) · max, count over frame (with `tie_free=True` it runs) · exp · ln · log10, log2 · log(base) · trigonometry · replace '' · re_extract · re_replace · hexdigest · rolling sum by time (with `tie_free=True` it runs) · time of day · time parts · compare times · try_cast |
<!-- coverage:end -->

The engines refuse what they can't do as Lean does: `<` on strings is
undefined in the model (it is NULL there, while SQL compares), and Snowflake
and Spark tables have no row order for FETCH, for the ties of a sort or a
window, or for the order a `SUM` or `AVG` of doubles adds in. See
[Engines and SQL](docs/guide.md#engines-and-sql).

## Development

To work on the project or run the tour from a clone, you need [uv](https://docs.astral.sh/uv/) for Python,
[elan](https://github.com/leanprover/elan) for Lean (elan is to Lean what
rustup is to Rust, or uv to Python), and Java 17 or 21 for the Spark tests:

```bash
brew install uv          # or: curl -LsSf https://astral.sh/uv/install.sh | sh
```
```bash
brew install openjdk@21  # or: sudo apt install openjdk-21-jre-headless
```

Homebrew's JDK is not on the `PATH`; point `JAVA_HOME` at it (in `~/.zshrc`):

```bash
export JAVA_HOME=/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home
```

Without a JVM the Spark tests are skipped and everything else runs.
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Open a new terminal so `lake` (Lean's build tool) is on your PATH, then run, from
the project root:

```bash
lake build                       # checks every proof and builds the substrait-check CLI
```
```bash
cd python && uv sync             # sverify with every extra, and the dev tools (pytest, hypothesis, …)
```
```bash
uv run pytest                    # all pass; the Spark tests skip without a JVM
```

`uv sync` installs `sverify` in editable mode, with every extra (below). Its build hook runs
`lake build substrait-check` and links `sverify/_bin/substrait-check` to the
result, so later `lake build`s take effect without reinstalling. To use a
different binary, set `SVERIFY_CHECK` to its path.

### Development tasks

Tasks are defined with [poe](https://poethepoet.natn.io) in `python/pyproject.toml`:

```bash
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
| `poe test` | Python tests, including the randomized engine tests, on every core |
| `poe test-core`, `test-datafusion`, `test-duckdb`, `test-polars`, `test-snowflake`, `test-spark` | The Python tests of one backend (`pytest -m <backend>`; see `python/tests/conftest.py`). CI runs one job per backend. |
| `poe notebooks` | Checks the tour notebooks and runs each one headless |
| `poe docs`, `poe docs_preview` | Builds the API reference site into `python/great-docs/_site` (or serves it locally). Needs [Quarto](https://quarto.org) and `uv sync --group docs`; not part of `qa` |

From the project root, use `uv run --project python poe -C python qa`. The Lean
tasks need `lake` on your PATH.

### The tour

The five notebooks in [`notebooks/`](notebooks) form a guided tour, starting at
[`01_duplicate_payments.py`](notebooks/01_duplicate_payments.py). Open the whole folder, so the
links between notebooks work:

```bash
uvx marimo edit --sandbox notebooks              # from the project root
```
```bash
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
| 5 | [Pipelines and engines](notebooks/05_pipelines_and_engines.py) | incremental views, nodes and sinks, DuckDB, Polars, DataFusion, Spark and Snowflake SQL, doubles, time and text |

[catalogue/backend_semantics.py](catalogue/backend_semantics.py) is a sixth marimo app outside the tour: one
expression asked of every engine. Under-the-hood detail is in
[docs/how-it-works.md](docs/how-it-works.md).

`poe notebooks` (part of `poe qa`) checks every notebook with `marimo check` and
runs it headless. The notebooks' tables come from `sverify.display`, which needs
marimo.

### Wheels

`uv build python --wheel` builds a wheel for the current platform. It bundles a
stripped `substrait-check`, so installing it needs neither Lean nor elan. The
[Wheels workflow](.github/workflows/wheels.yml) builds and tests wheels for Linux
(x86_64, aarch64) and macOS (arm64, x86_64). A `v*` tag that matches the
version in `python/pyproject.toml` also publishes them to PyPI.

`uv build python` also builds the sdist. It carries the Lean project under
`lean/`, and `uv build` makes the wheel from it, so the sdist is checked on
every build. Installing from the sdist (on a platform without a wheel) needs
elan; the build hook runs `lake build` there.

To run your own scripts with the package available, from the project root:

```bash
uv run --project python python my_pipeline.py
```

### Troubleshooting

* `lake: command not found`: open a new terminal, or call `~/.elan/bin/lake`.
* `no configuration file …lakefile`: run `lake` from the project root, where `lakefile.toml` is.
* `… does not exist` for a notebook or `--project` path: those paths are relative to the
  project root, and `python/` is not the root.
* Why DataFusion 51? Ibis 12's DataFusion backend fails to connect with
  DataFusion 52 and later (a changed user-defined-function API).

## Possible next steps

The open work is tracked on GitHub:

* [#29, the roadmap](https://github.com/AlexanderNenninger/substrait-lean/issues/29):
  closing the gaps between the model and the engines, engine profiles, and the
  optimizations of [docs/optimizations.md](docs/optimizations.md).
* [#60, Ibis API coverage](https://github.com/AlexanderNenninger/substrait-lean/issues/60):
  the operations the coverage table above marks ✗, ranked by how many queries
  of the [catalogue](catalogue/FINDINGS.md) they block.
* [#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85): proved
  error bounds, so that sharded `SUM` and `AVG` of doubles can be allowed.
* [#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63): testing
  the Snowflake SQL on a real account; today it only runs on an emulator.

Longer-term directions:

1. Non-linear incremental operators. Aggregates (SUM and COUNT per group
   are linear over Z-sets), `DISTINCT`, semi and left joins, windows.
2. Completeness. Contracts say what every output row satisfies; the
   converse ("no window is lost") is a Lean theorem per plan today
   (`IoT.window_complete`); the checker doesn't report it yet.
3. Translation validation. Given a plan and its optimized form, have Lean
   check that they are equivalent. A decision procedure for the conjunctive
   fragment would mirror Cosette and HoTTSQL.
4. Real types. A typing judgement over Substrait types (decimals, dates,
   nullability), with `eval` proven to respect it.
5. Mathlib `Multiset` or K-relations. Move bag equivalence to quotients, or
   generalize to semiring-annotated relations as HoTTSQL and provenance do.

## License

Sverify is licensed under the [Mozilla Public License 2.0](LICENSE) (MPL-2.0).
You can use it in any product, open or proprietary, and your own code stays
yours. If you distribute a modified version of sverify's own files, those
files stay under the MPL and you share their source. The license applies file
by file, so it never reaches the code around them.

`python/src/sverify/ibis_substrait/` is derived from
[ibis-substrait](https://github.com/ibis-project/ibis-substrait) and stays
under the [Apache License 2.0](python/src/sverify/ibis_substrait/LICENSE).
