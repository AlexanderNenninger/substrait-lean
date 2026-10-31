# substrait-lean

**Keep query results up to date without recomputing them, with updates proven correct.**

Say you have a dashboard table built from a join over a few million orders, and
a hundred orders change every hour. Recomputing the whole join each time is
slow. Hand-written incremental logic ("only process rows where `updated_at` is
newer than…") is fast, but it tends to go wrong silently: deletes are missed,
late rows are skipped, a join gets a new match.

This project gives you a third option. You write the query once, in Ibis or SQL,
and `sverify` maintains the result from the inserts and deletes alone.
The update logic comes from a delta plan that is **mathematically proven to give
the same result as a full recompute**. The proof is in [Lean](https://lean-lang.org),
a proof assistant: a program that checks every step of a proof, so you don't
have to take the math on trust.

```python
view = sv.IncrementalView(con, big_orders, "big_orders")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 50)], deletes=[(1, "ada", 30)])})
# `big_orders` now equals what a full recompute would give, with no recompute.
```

Underneath, queries travel as [Substrait](https://substrait.io), an open,
engine-neutral format for query plans. `sverify` writes your query as a
Substrait plan, Lean checks it and computes the proven update plan, and
[DuckDB](https://duckdb.org) runs that plan (or Polars, DataFusion or Spark).

The same checker does more than incremental views:

* **Contracts.** State what you assume about the inputs (`requires`) and what
  the output guarantees (`ensures`); the postconditions are proved before the
  pipeline runs, including that no division by zero, overflow or bad cast can
  happen. Contracts compose across steps and travel with Delta Lake and
  Iceberg tables.
* **Several engines, one semantics.** A checked plan runs on DuckDB,
  Polars, DataFusion or Spark, or is written as Snowflake SQL. Each translation
  either keeps the Lean semantics (NULLs, integer division, NaN, ties) or
  refuses the plan, and differential tests compare every engine with Lean.
* **Proved optimizations.** A plan can be split across shards (Delta or
  Iceberg partitions, files) and combined, with a proof that the result is the
  same; run-time checks can be dropped where a contract proves them
  unnecessary. See [docs/optimizations.md](docs/optimizations.md).

**New here?** [The tour](notebooks/00_start_here.py) is a series of interactive
[marimo](https://marimo.io) notebooks, one per feature, that you can work through
in order: plans and proofs, the checker, contracts, keys, doubles and time,
runtime errors, windows and ASOF joins, composition, incremental views,
pipelines, engines, a complete pipeline end to end, and what exactly is
proved, with two appendices on how DataFusion and the other engines differ
from the model. No prior knowledge of formal verification or data engineering is
assumed. See [The tour](#the-tour) for how to open it.

## Setup

You need [uv](https://docs.astral.sh/uv/) for Python,
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

Open a new terminal so `lake` (Lean's build tool) is on your PATH. Then, from
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

### Extras

The core of `sverify` runs on DuckDB: contracts, incremental views, the table
store behind `sverify.connect()`, and the SQL dialects (DuckDB, Snowflake and
Spark SQL are generated without any extra). The other engines and the table
formats are extras:

| Extra | Adds |
|---|---|
| `datafusion` | `engine="datafusion"`, and compiling SQL strings (DataFusion's Substrait producer) |
| `polars` | `engine="polars"` (`sverify.polars_engine`) |
| `spark` | `sverify.spark_engine`, which runs plans on a Spark session (needs Java 17 or 21) |
| `delta` | `sverify.io.DeltaSource`, `DeltaSink` |
| `iceberg` | `sverify.io.IcebergSource`, `IcebergSink` |
| `all` | all of the above |

```bash
pip install 'sverify[polars,spark]'
```

Using a feature without its extra raises an `ImportError` that names it.

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

From the project root, use `uv run --project python poe -C python qa`. The Lean
tasks need `lake` on your PATH.

### The tour

The notebooks in [`notebooks/`](notebooks) form a guided tour, starting at
[`00_start_here.py`](notebooks/00_start_here.py). Open the whole folder, so the
links between chapters work:

```bash
uvx marimo edit --sandbox notebooks              # from the project root
```
```bash
uvx marimo run --sandbox --include-code notebooks   # read-only apps
```

`--sandbox` runs each notebook in its own environment, with `sverify` installed
from `python/` as declared in the notebook's header; the first start takes a
minute. Build the checker first (`lake build`). To use the project's own
environment instead: `uv run --project python marimo edit notebooks`.

| | Chapter | What it covers |
|---:|:---|:---|
| 0 | [Start here](notebooks/00_start_here.py) | what the library does, and how to use the tour |
| 1 | [Plans, meaning and proofs](notebooks/01_plans_and_proofs.py) | Substrait plans, Lean's interpreter, theorems, NULL |
| 2 | [The checker](notebooks/02_the_checker.py) | `substrait-check`: well-formedness, Lean as a reference engine, Ibis coverage |
| 3 | [Contracts](notebooks/03_contracts.py) | `requires`/`ensures`, abstract interpretation, `on_unproved` |
| 4 | [Keys and relations](notebooks/04_keys_and_relations.py) | `sv.unique`, facts between columns, joins |
| 5 | [Doubles, time and text](notebooks/05_values.py) | NaN and −0.0, timestamps and intervals, calendar functions, strings |
| 6 | [Runtime errors](notebooks/06_runtime_errors.py) | division by zero, overflow, casts; proving they can't happen |
| 7 | [Windows and ASOF joins](notebooks/07_windows_and_asof.py) | LAG, LEAD, ROW_NUMBER, ties; aligning two sensors |
| 8 | [Composing contracts](notebooks/08_composition.py) | proving one step's preconditions from the previous step |
| 9 | [Incremental views](notebooks/09_incremental_views.py) | Z-sets, delta rules, `IncrementalView` |
| 10 | [Pipelines](notebooks/10_pipelines.py) | views over views, fallbacks, contracts that hold in every state |
| 11 | [Engines and SQL](notebooks/11_engines.py) | DataFusion, Polars, DuckDB; SQL for DuckDB, Snowflake and Spark |
| 12 | [A complete pipeline](notebooks/12_fitness.py) | heart rate during workouts, end to end |
| 13 | [What is proved, what is trusted](notebooks/13_trust.py) | the trusted boundary, a glossary and a map of the code |
| 14 | [DataFusion's surprising semantics](notebooks/14_datafusion_semantics.py) | appendix: every DataFusion quirk, checked against the Lean model |
| 15 | [One expression, many engines](notebooks/15_backend_semantics.py) | appendix: DataFusion, DuckDB, Polars, Snowflake and Ibis, question by question |

`poe notebooks` (part of `poe qa`) checks every chapter with `marimo check` and
runs it headless. The chapters' tables come from `sverify.display`, which needs
marimo.

### Troubleshooting

* **`lake: command not found`**: open a new terminal, or call `~/.elan/bin/lake`.
* **`no configuration file …lakefile`**: run `lake` from the project root, where `lakefile.toml` is.
* **`… does not exist`** for a notebook or `--project` path: those paths are relative to the
  project root, not to `python/`.
* **Why DataFusion 51?** Ibis 12's DataFusion backend fails to connect with
  DataFusion 52 and later (a changed user-defined-function API).

## Examples

### An incrementally maintained join

```python
import ibis
import sverify as sv

con = sv.connect()  # tables in memory; plans run on DuckDB by default
sv.create_table(con, "orders", ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
                [(1, "ada", 30), (2, "bob", 5)])
sv.create_table(con, "customers", ibis.schema({"name": "string", "city": "string"}),
                [("ada", "Paris")])

orders, customers = con.table("orders"), con.table("customers")
big_orders = (
    orders.filter(orders.amount > 10)
    .join(customers, orders.customer == customers.name)
    .select(orders.id, customers.city, orders.amount)
)

view = sv.IncrementalView(con, big_orders, "big_orders")
view.rows()                      # [(1, 'Paris', 30)]

# Changes to both tables at once: order 1 leaves, order 3 arrives,
# and bob's new customer row makes his order match the join.
view.apply({
    "orders": sv.Changes(inserts=[(3, "bob", 50)], deletes=[(1, "ada", 30)]),
    "customers": sv.Changes(inserts=[("bob", "Rome")]),
})
view.rows()                      # [(3, 'Rome', 50)]
assert view.rows() == view.recompute()

# An update is a delete plus an insert.
view.apply({"orders": sv.Changes(deletes=[(3, "bob", 50)], inserts=[(3, "bob", 70)])})
view.rows()                      # [(3, 'Rome', 70)]
```

`apply` also updates the base tables. A batch is computed completely before
anything is replaced: if anything fails, for example deleting a row that doesn't
exist, nothing changes. The view is also a table you can query:
`con.table("big_orders")`.

Plain SQL works too: `sv.IncrementalView(con, "select ... from ...", "name")`.
More example pipelines, with unbound tables you can reuse on any connection, are
in [`sverify/examples.py`](python/src/sverify/examples.py).

### What is supported, and what is refused

Supported: filters, computed columns, inner joins (including self-joins), cross
joins and `UNION ALL`. Anything outside that is refused up front instead of
being maintained incorrectly (window functions can be verified with contracts,
but not maintained incrementally yet):

```python
sv.IncrementalView(con, orders.limit(5), "top5")
# NotIncremental: not incrementally maintainable (left, semi or anti join, DISTINCT,
# fetch, window or aggregate)

totals = orders.group_by("customer").aggregate(total=orders.amount.sum())
sv.IncrementalView(con, totals, "totals")
# NotIncremental: ...
```

Aggregates (`GROUP BY` with `SUM`, `COUNT`, …) can be verified with contracts,
but are not maintained incrementally yet; see
[Possible next steps](#possible-next-steps).

How much of the Ibis API gets through, from
[`sverify/coverage.py`](python/src/sverify/coverage.py) (regenerate with
`uv run python -m sverify.coverage --write-readme` in `python/`):

<!-- coverage:start -->
68 of 82 probed Ibis operations reach the checker (✓ verified, ✗ rejected by the checker, – fails in Ibis or DataFusion; *inc.* marks incremental maintenance).

| Area | Operations |
|---|---|
| rows | ✓ filter, select *inc.* · ✓ mutate *inc.* · ✓ drop, rename *inc.* · ✓ drop_null *inc.* · ✓ isnull *inc.* · ✓ between *inc.* · ✓ isin *inc.* · ✓ notin *inc.* · ✓ ifelse *inc.* · ✓ cases *inc.* · ✓ order_by *inc.* · ✓ limit · ✓ limit with offset · ✓ order_by + limit · ✗ sample |
| joins | ✓ inner join *inc.* · ✓ non-equi join *inc.* · ✓ cross join *inc.* · ✓ left join · ✓ right join · ✓ outer join · ✓ semi join · ✓ anti join · ✓ isin subquery · ✓ union all *inc.* · ✓ union distinct · ✓ intersect · ✓ difference |
| aggregation | ✓ count() · ✓ group_by sum · ✓ count, max, mean · ✓ nunique · ✓ sum(where=) · ✓ having · ✓ value_counts · ✓ distinct · ✗ distinct(on=) · ✗ std · ✗ collect · ✗ scalar subquery · ✗ unnest |
| windows | ✓ row_number · ✓ lag · ✗ rank · ✗ dense_rank · ✗ cumsum · ✗ sum over group · ✗ rolling mean (rows) · ✗ rolling mean (interval) · ✗ ntile · ✗ first |
| numbers | ✓ +, -, * *inc.* · ✓ float division *inc.* · ✓ integer division *inc.* · ✓ mod *inc.* · ✓ abs *inc.* · ✓ round *inc.* · ✓ ceil, floor *inc.* · ✓ power *inc.* · ✓ greatest *inc.* · ✓ least *inc.* · ✓ clip *inc.* · ✓ cast int → double *inc.* · ✓ cast int → string *inc.* · ✓ cast double → int *inc.* |
| nulls | ✓ fill_null *inc.* · ✓ coalesce *inc.* · ✓ nullif *inc.* |
| strings | ✓ upper *inc.* · ✓ length *inc.* · ✓ concat *inc.* · ✓ substr *inc.* · ✓ contains *inc.* · ✓ startswith *inc.* · ✓ like *inc.* · ✓ re_search *inc.* · ✓ strip *inc.* |
| time | ✓ timestamp + interval *inc.* · ✓ compare with literal *inc.* · ✓ year *inc.* · ✓ date *inc.* · ✓ truncate *inc.* |

Every engine runs the plans of the 68 verified operations, except:

| Engine | Runs | Refuses |
|---|---|---|
| Polars | 67 | non-equi join |
| DuckDB | 67 | non-equi join |
| Snowflake | 60 | order_by (with `tie_free=True` it runs) · limit · limit with offset · order_by + limit · non-equi join · count, max, mean · row_number (with `tie_free=True` it runs) · lag (with `tie_free=True` it runs) |
| Spark | 60 | order_by (with `tie_free=True` it runs) · limit · limit with offset · order_by + limit · non-equi join · count, max, mean · row_number (with `tie_free=True` it runs) · lag (with `tie_free=True` it runs) |
<!-- coverage:end -->

The engines refuse what they cannot do as Lean does: `<` on strings is
undefined in the model (it is NULL there, while SQL compares), and Snowflake
and Spark tables have no row order for FETCH, or for the ties of a sort or a window, to
follow, nor for the order a `SUM` or `AVG` of doubles adds in. See
[Engines](#engines).

### Pre- and postconditions on a transformation

Declare what you assume about the inputs (`requires`) and what the output
guarantees (`ensures`). Postconditions are **proved** before the expression is
returned, not tested:

```python
from ibis import _
import sverify as sv

@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

expr = doubled(orders)          # proves all three postconditions, then returns the expression
print(doubled.last_report)
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
# ensures id IS NOT NULL: proved
# known about the output:
#   id: any integer
#   doubled: an integer ≥ 22
```

Lean worked out that `doubled` is at least 22: the filter keeps only `amount > 10`,
and doubling preserves that. A postcondition that doesn't follow is refused, along with
the reason:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)

plus_one(orders)
# VerificationError: could not prove: (_.total > 5) (it is TRUE or FALSE)
#   known about the output: total: an integer ≥ 1
```

* **Conditions** can be Ibis expressions (`_.amount >= 0`, or a function of the
  table) or SQL snippets (`"amount >= 0"`). Here's a SQL transformation:
  `sv.verify("select ... from orders where ...", tables={"orders": orders}, ensures=["rest >= 0"])`.
* **Preconditions** are assumptions about data that comes from outside. When the
  inputs are bound to a backend (real tables), they are checked on the data at
  call time and raise `PreconditionError` if violated.
* **Unproved postconditions** raise `VerificationError` by default. With
  `on_unproved="runtime"` they are checked on the output data instead, raising
  `PostconditionError` on a violation. With `on_unproved="warn"` you get a warning.
* **What Lean tracks** per column: whether it can be NULL, an integer range, which
  booleans it can be, and whether it can be a string. Filters like
  `amount > 10`, `amount <= 50`, `x = 3` and `x IS NOT NULL` refine those facts. It
  also understands arithmetic (multiplication by constants), comparisons, `AND`/`OR`/`NOT`
  with SQL NULL semantics, `CASE`, joins and `UNION ALL`. Column schemas count too:
  a non-nullable column (`!int64`) is never NULL.
* **Relations and excluded values:** join and filter conditions such as
  `w1.ts = w0.ts + 60`, `a.ts = b.ts`, `t0 < t1` or `value != -9999` become facts
  about the row. Joining on `a.ts = b.ts` makes both sides non-NULL. Postconditions
  such as `t1 - t0 == 60`, `t1 > t0` or `value != -9999` follow from those facts.
  So a windowed IoT training set (sensors joined on time, error values dropped,
  consecutive timesteps joined) is proved complete, error-free and consecutive. See
  `test_iot_windows_are_proved_complete_and_consecutive` in `python/tests/test_contracts.py`.
* **Keys:** `sv.unique("ts")` in `requires` says the producer sends at most one
  row per `ts` (checked on the data when bound). In `ensures` it is proved, since
  keys survive filters, projections and joins whose condition pins down the other
  side's key (`a.ts = b.ts`, `w1.ts = w0.ts + 60`).
* **Window functions:** `LAG`, `LEAD` and `ROW_NUMBER` over `PARTITION BY … ORDER BY …`
  (any directions, NULLs first or last, offsets and defaults). Lean knows that
  `LAG(ts)` comes from an earlier row of the same partition, that a lagged
  partition column equals the row's own, and that `ROW_NUMBER()` is positive
  (Ibis numbers from 0). With a key on the partition and the (single) order
  column, earlier means strictly earlier: `prev_ts < ts`, and a computed
  `gap = ts - prev_ts` is positive. Guard the first row's NULL with `isnull() | …`:

  ```python
  @sv.transform(
      requires={"readings": [sv.unique("sensor", "ts"), _.sensor.notnull(), _.ts.notnull()]},
      ensures=[_.prev_ts.isnull() | (_.prev_ts < _.ts), _.rn >= 0],
  )
  def with_previous(readings):
      w = ibis.window(group_by=readings.sensor, order_by=readings.ts)
      return readings.select("sensor", "ts", prev_ts=readings.ts.lag().over(w),
                             rn=ibis.row_number().over(w))
  ```

  **Ties are refused.** If two rows of a partition can have the same `ORDER BY`
  values, DataFusion decides which comes first, and `LAG` depends on that.
  Unless `requires` gives a key on (a subset of) the partition and order columns,
  every postcondition is reported as `undetermined` and `report.deterministic` is
  `False`. `window_tiebreak` proves that with such a key, every way of breaking
  ties gives the same rows.
* **ASOF joins** align sensors with different sampling rates. `sv.asof_join` matches
  each left row with the latest right row of the same `by` values at or before
  it, at most `tolerance` earlier. DataFusion has no ASOF join (and Ibis's
  `asof_join` compiles to DuckDB syntax), so it is built from a range join and
  `ROW_NUMBER`, which Lean checks like any other plan:

  ```python
  # Accelerometer at 100 Hz, gyroscope at 130 Hz.
  @sv.transform(
      requires={"acc": [sv.unique("device", "ts"), _.device.notnull(), _.ts.notnull()],
                "gyr": [sv.unique("device", "ts")]},
      ensures=[sv.unique("device", "ts"),                       # one row per acc sample
               _.ts_right.isnull() | (_.ts_right <= _.ts),       # never from the future
               _.ts_right.isnull() | (_.ts_right >= _.ts - ibis.interval(milliseconds=10))],
  )
  def aligned(acc, gyr):
      return sv.asof_join(acc, gyr, on="ts", by="device",
                          tolerance=ibis.interval(milliseconds=10))
  ```

  All three are proved, for `how="left"` (the default, keeping unmatched rows
  with NULLs) and `how="inner"`. The right side needs a key on `(by, on)`:
  otherwise two gyroscope readings at the same instant tie, and the result is
  `undetermined`. (`sverify` lifts Ibis's refusal of sub-second interval literals
  for DataFusion, which supports them.)
* **Doubles, timestamps, dates:** comparisons with constants are exact, including
  sentinels like `-9999.0`, `isnan()`, `INTERVAL '60' SECOND` and ranges like `v > 0.5`.
  Double arithmetic (`v * 2.5`) is only known to give "some double", because rounding
  isn't modelled; negation, `ABS`, `FLOOR`, `CEIL` and `ROUND` keep bounds. Doubles compare as SQL engines compare them: there is one
  zero (−0.0 *is* 0.0, so `-0.0 >= 0` holds and −0.0 never shows in a result)
  and one NaN, which equals itself and sorts above every number (so `v > 0`
  keeps NaN rows). See [Doubles](#doubles-one-zero-and-one-nan).
* **Not tracked yet:** relations that need more than "column plus constant"
  (`a < 2 * b`), string contents, DECIMAL columns, and counts across rows.
  Strict window order needs a single `ORDER BY` column (with several, rows
  are only ordered lexicographically).

  [Chapter 12 of the tour](notebooks/12_fitness.py) walks through a complete example.

### Composing contracted transformations

Contracted transformations compose. When one's result feeds another, the
downstream precondition is **proved** from the upstream contract, never checked
on the data, and the downstream function is proved assuming only what the
upstream one guarantees:

```python
@sv.transform(requires={"orders": [_.amount >= 0, sv.unique("id")]},
              ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")])
def paid(orders):
    return orders.filter(orders.amount.notnull())

@sv.transform(requires={"t": [_.amount >= 0, _.amount.notnull()]},
              ensures=[_.doubled >= 0, _.doubled.notnull()])
def doubled(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)

expr = doubled(paid(orders))
print(doubled.last_report)
# requires paid: (_.amount >= 0)          ← what `paid` guarantees, not `orders`
# requires paid: _.amount.notnull()
# requires paid: unique(id)
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
```

If the upstream contract doesn't imply the downstream precondition, the call
fails and names the broken link:

```python
@sv.transform(ensures=[_.amount.notnull()])
def not_null(orders):
    return orders.filter(orders.amount.notnull())

doubled(not_null(orders))
# CompositionError: doubled needs (_.amount >= 0) (it is TRUE or FALSE) on 't';
#   not_null only guarantees _.amount.notnull()
```

A precondition can also follow from more than the upstream `ensures`: it is
proved as an extra postcondition of the upstream transformation, from its own
preconditions. Keys (`sv.unique`) propagate the same way. Plain Ibis steps in
a chain (`doubled(paid(orders).filter(...))`) carry no guarantees: what
follows from their own operations is proved, and the rest is checked on the
data like a base table's. `sv.contracts.provenance(expr)` shows what a
contracted result assumed and guarantees.

### Contracted pipelines, kept up to date

A `Pipeline` maintains views that read each other. Each view's change is
handed to the views that read it, so intermediate results are computed once
and shared. Views of contracted transformations keep their guarantees in every
state: their preconditions on the base tables are checked in full once, then
only on each batch (row conditions on the inserted rows, keys against the keys
the batch keeps):

```python
pipe = sv.Pipeline(con)
base = pipe.view("base", doubled(paid(con.table("orders"))))
b, customers = base.table, con.table("customers")
cities = pipe.view("cities", b.join(customers, b.customer == customers.name)
                              .select("id", "city", "doubled"))
located = pipe.view("located", b.left_join(customers, b.customer == customers.name)
                                .select("id", "city"))
pipe.fallbacks
# {'located': 'not incrementally maintainable (left join, fetch or window)'}

pipe.apply({"orders": sv.Changes(inserts=[(3, "ada", 7)], deletes=[(2, "bob", 5)]),
            "customers": sv.Changes(inserts=[("bob", "Rome")])})
cities.rows()                    # [(1, 'Paris', 60), (3, 'Paris', 14)]

pipe.apply({"orders": sv.Changes(inserts=[(1, "cy", 4)])})
# PreconditionError: 1 inserted key(s) of orders violate unique(id)
```

A view reads base tables and earlier views (`view.table`). A contracted
transformation applied to `view.table` builds on that view's guarantees, as
in a direct composition. A view without a delta rule (left join, fetch,
window) is recomputed and diffed; its change still flows to the views
downstream, and `pipe.fallbacks` lists such views. `sv.IncrementalView` is a
pipeline with one view, and refuses a query without delta rules.

### Delta Lake and Iceberg tables

`sverify.io` reads and writes Delta Lake (delta-rs) and Iceberg (pyiceberg)
tables. Sources hand Arrow tables to the pipeline, so every engine works. A
table format plays three roles:

* **A change source.** `pipe.source` loads a snapshot and records its
  version (`orders@v1`). `pipe.refresh()` reads the Delta Change Data Feed
  from the recorded version to the latest (`insert`/`update_postimage` +1,
  `delete`/`update_preimage` −1), applies it, and records the new version in
  the same commit. A failed refresh changes nothing, so a retry never applies
  a batch twice. Where the history is gone (CDF off, files vacuumed, log
  removed), the new snapshot is diffed against the view's state, the views
  reading it are recomputed, and the report says so.
* **A source of preconditions.** `requires` conditions are proved from
  metadata where possible: schema nullability (`nullable=false`, Iceberg
  `required`), Delta CHECK constraints, and per-file statistics (min/max for
  integers, dates and timestamps; NULL counts for every column). A batch only
  uses the statistics of the files it added. Keys are always checked on the
  data, since neither format enforces them.
* **A sink that carries the contract.** `DeltaSink` writes a view in one
  commit per state, exactly once (Delta's transaction identifiers, keyed by
  the sum of the source versions). The proved guarantees become NOT NULL
  columns and CHECK constraints, and the commit metadata records the plan
  hash, the source versions and the contract. A downstream job that reads the
  table gets its preconditions from them.

```python
import pyarrow as pa
from deltalake import DeltaTable, write_deltalake
from sverify.io import DeltaSink, DeltaSource

schema = pa.schema([pa.field("id", pa.int64(), nullable=False),
                    pa.field("customer", pa.string()), pa.field("amount", pa.int64())])
def batch(*rows):
    return pa.Table.from_pylist([dict(zip(schema.names, r)) for r in rows], schema=schema)

write_deltalake("orders", batch((1, "ada", 5), (2, "bob", 7)),
                configuration={"delta.enableChangeDataFeed": "true"})
DeltaTable("orders").alter.add_constraint({"positive": "amount >= 0"})

@sv.transform(
    requires={"orders": [_.id.notnull(), _.amount >= 0, _.amount <= 1000, sv.unique("id")]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), sv.unique("id")],
)
def doubled(orders):
    return orders.select(orders.id, orders.customer, doubled=orders.amount * 2)

pipe = sv.Pipeline(sv.connect())
big = pipe.view("big", doubled(pipe.source("orders", DeltaSource("orders"))))
for p in pipe.preconditions: print(p)
# orders: unique(id) (checked on data)
# orders: _.id.notnull() (schema)
# orders: (_.amount >= 0) (Delta constraint)
# orders: (_.amount <= 1000) (file stats @v1)

sink = DeltaSink("big", big)
sink.write()            # big from orders@v1: created v2, 2 row(s) written, 0 deleted

dt = DeltaTable("orders")
write_deltalake(dt, batch((3, "cy", 4)), mode="append")
dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
print(pipe.refresh())
# orders@v1→v3: 2 insert(s), 1 delete(s); Δ trusted as coming from Delta CDF v1→v3
# requires orders: _.id.notnull() (schema)
# requires orders: (_.amount >= 0) (Delta constraint)
# requires orders: (_.amount <= 1000) (file stats @v3 (new files))
# requires orders: unique(id) (checked on data)
# view big: orders@v3
sink.write()            # big from orders@v3: merge v3, 2 row(s) written, 1 deleted

DeltaTable("big").metadata().configuration["delta.constraints.sverify_1"]   # 'doubled >= 0'
DeltaSource("big").contract()
# Contract(view='big', plan='cbaa09dd…', sources={'orders': 3}, epoch=3,
#          not_null=['doubled'], checks={'sverify_1': 'doubled >= 0'}, unique=[['id']])

# Another job builds on big's contract instead of checking big's data:
@sv.transform(requires={"t": [_.doubled >= 0, _.doubled.notnull()]}, ensures=[_.half >= 0])
def halved(t):
    return t.select(t.id, half=t.doubled // 2)

job2 = sv.Pipeline(sv.connect())
halves = job2.view("halves", halved(job2.source("big", DeltaSource("big"))))
for p in job2.preconditions: print(p)
# big: _.doubled.notnull() (schema)
# big: (_.doubled >= 0) (Delta constraint)
```

`pipe.refresh(audit=True)` also compares the batch with the new snapshot
before committing, and every view with its recomputation afterwards
(`AuditError`). Iceberg works the same way with `IcebergSource(catalog,
"db.orders")` and `IcebergSink`: versions are snapshot sequence numbers, a
run of appends is read from the files those snapshots added, and anything
else (row-level deletes, overwrites) is a diff of the two snapshots, which the
report names. Iceberg has no CHECK constraints, so the sink keeps the
contract in the table properties and every snapshot summary, and a reader
uses it only while every snapshot of the table was written under it.

What is trusted: that the change feed turns the old snapshot into the new
one (each report says "Δ trusted as coming from …"), that writers enforce
nullability and constraints, and that file statistics are correct (Delta's
millisecond timestamp maxima are widened by 999 µs). What is proved: given a
correct feed, the views are maintained correctly (`Rel.cdf_sound`); a
snapshot diff is a correct feed (`ChangeFeed.of_diff`); per-file bounds bound
the table and an append's rows (`stats_table`, `stats_append`); and each
precondition follows from the metadata facts (`contract_sound`).

### Sharded evaluation

`sverify.partition` runs a plan on each shard of its data (a Delta or Iceberg
partition, a file, a worker's slice) and combines the results. Lean splits
the plan and proves the combined result equals the plan's result on all the
data (`Rel.shardSplit_sound`):

```python
import sverify.partition as sp

sp.split(plan, sharded=["orders"])            # Split(mode='two_phase', ...) or NotShardable
sp.run_sharded(plan, shards, sharded=["orders"], broadcast={"customers": customers})
```

Filters, projections, sorts, unions and joins with a broadcast table run on
every shard and are concatenated. `COUNT`, integer `SUM`, `MIN` and `MAX` run
in two phases: each shard aggregates, then the partial rows are combined.
Refused, with the reason: `SUM`/`AVG` of doubles (the rounding would depend
on the split; issue #85), `DISTINCT`, windows, `FETCH` and joins of two
sharded tables. A partial integer sum that leaves 64 bits is an error, never a
wrong answer. Shards run on Polars, in parallel threads.

Run-time checks are the other proved optimization: the SQL and the Polars
expressions guard every operation that could overflow or fail. When the
contract report says `guard_free`, `to_sql(..., guards=False)` (and
`guards=False` for the Polars and DuckDB runners) leaves them out
(`Rel.guardFree_sound`). [docs/optimizations.md](docs/optimizations.md)
compares these with what the engines already do, and ranks what is next.

### Checking a query plan

`substrait-check` reads any Substrait JSON plan, shows it in readable form,
and reports what was verified about it:

```python
plan = sv.substrait_json(con, "select id, amount * 2 as doubled from orders where amount > 10")
open("plan.json", "w").write(plan)
```
```text
$ .lake/build/bin/substrait-check plan.json
Emit [1, 2]                    ← output columns: id, doubled
  Project +[($0 * 2)]          ← append amount * 2
    Filter (10 < $0)           ← amount > 10
      Emit [2, 0]              ← read only (amount, id)
        Read orders
tables: orders(3)
arity: 2
well-formed: yes               ← every column reference exists (a check proven correct)
incremental: yes               ← a proven update plan exists
roundtrip: ok                  ← writing the plan back out reproduces it
rows (0):                      ← named tables carry no data here, only their schema
```

Columns are referred to by position (`$0` is the first column), which is how
Substrait works.

### How do I know it's right?

* **Proofs**: `lake build` re-checks every theorem. The main ones say that the
  update plan computes exactly the change to the result, and that running it on
  DataFusion with the weight-column encoding gives that result. See
  [Proven theorems](#proven-theorems).
* **Randomized testing**: `uv run pytest` generates random tables and random batches of
  inserts and deletes, including NULLs and duplicates. After every batch it
  checks that the maintained result equals a full recompute. This covers the parts
  the proofs don't: the JSON translation, the Python glue and the engine itself.

## The formal side

The rest of this README is for people who want to look under the hood.

```bash
lake build                                                  # proofs + CLI
tests/run.sh                                                # golden tests for the CLI
```

There are no dependencies beyond Lean core (no Mathlib yet), so the build takes seconds.

## Checking real plans

`substrait-check plan.json` reads a Substrait plan in protobuf-JSON form, as
produced by `sverify`'s Ibis producer or DataFusion's Substrait producer
(Substrait 0.77). It then:

1. translates it into the formal `Rel` model, or rejects anything outside the fragment (exit 1);
2. decides `Rel.WF` with `checkWF`, which is proven equivalent (`checkWF_iff`), and
   checks that `RelRoot.names` match the output arity (exit 2 if ill-formed);
3. evaluates the plan. Named tables are schema-only (arity from `baseSchema`, no rows),
   so only `VirtualTable` data produces output rows.

```text
$ substrait-check tests/fixtures/virtual_left_join.json
Emit [0, 4]
  Project +[IF IS_NULL($3) THEN "unknown" ELSE $3]
    LeftJoin ($1 = $3)
      Values[3] 3 row(s)
      Values[1] 2 row(s)
arity: 2
well-formed: yes
rows (3):
  (1, "ada")
  (2, "unknown")
  (3, "ada")
```

Supported: `read` (named / virtual table, `filter`, `projection` mask), `filter`, `project`, `cross`,
`join` (inner, left), `fetch` (literal offset/count), `set` (union all), and
`RelCommon.emit`. Expressions: literals (bool, integers, string, null), direct
field references, `ifThen`, casts of integer literals to integer types, and scalar functions `and`, `or`, `not`, `is_null`,
`is_not_null`, `negate`, `add`, `subtract`, `multiply`, `equal`, `not_equal`,
`lt`, `gt`, `lte`, `gte`, matched by name in `extensions`.

The CLI also reports whether the plan is in the incremental fragment
(`isIncremental`, proven equivalent to `Rel.Incremental`) and whether writing
it back out as JSON and re-parsing gives the same `Rel` (`roundtrip: ok`).

The parser ([Parse.lean](SubstraitLean/Parse.lean)) and writer
([Write.lean](SubstraitLean/Write.lean)) are **trusted, unverified code**. The
proofs are about `Rel`, so a parser bug would make the CLI check the wrong plan.
The golden tests in `tests/fixtures` are the guard against that. The
`df_*.json` fixtures are real plans: the Ibis pipelines in
`sverify/examples.py`, compiled by Ibis and DataFusion
(`python/scripts/capture_fixtures.py`). The others are hand-written.

## Incremental views in Python

`python/` holds `sverify`, which maintains query results incrementally on
DuckDB (by default), Polars or DataFusion, using delta plans from Lean:

```python
import sverify as sv
from sverify.examples import PIPELINES, create_tables

con = sv.connect()          # Arrow tables; plans run on DuckDB
create_tables(con, orders_rows=[(1, "ada", 30)], customers_rows=[("ada", "Paris")])
view = sv.IncrementalView(con, PIPELINES["inner_join"], "v")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 7)], deletes=[(1, "ada", 30)]),
            "customers": sv.Changes(inserts=[("bob", "Rome")])})
assert view.rows() == view.recompute()
```

The query can be an Ibis expression or a SQL string.

How it works:

1. The query becomes a Substrait plan: an Ibis expression through the vendored
   Ibis producer (below), a SQL string through DataFusion's Substrait producer.
2. `substrait-check --delta` compiles the plan with `Rel.delta`, splits it into
   union-free terms (`Rel.terms`) and applies the weight-column encoding
   (`Rel.weighted`). It prints one Substrait plan per term, after checking each
   one is incremental and well-formed. The plans are union-free because
   DataFusion's Substrait consumer loses table qualifiers at a `UNION ALL`,
   and the duplicate column names then break a later join.
3. For each change batch, `sverify` registers the change tables `t$delta` (rows
   plus `__weight` = ±1), runs every term on the connection's engine (DuckDB by
   default; on DataFusion with its Substrait consumer), sums the weights per
   row, and merges the result into the view.

`python/tests/test_incremental.py` is a differential test (with `hypothesis`):
after random insert/delete batches, the maintained view must equal the query
recomputed from scratch. It runs every pipeline in `sverify/examples.py`:
filters and projections, inner joins, self-joins, `UNION ALL`, cross products,
and a filter-join-compute chain. It also runs one plain-SQL query, so the SQL
entry point stays covered.

**Connections.** `sv.connect(engine=...)` gives a `Connection`: the Arrow
tables (`sv.create_table`, `con.arrow`), the engine plans run on, and Ibis
tables bound to them (`con.table(name)`, through an in-memory Ibis DuckDB
backend that views the Arrow tables, so Ibis's own `.to_pyarrow()` works and
contracts find a table's data). `con.datafusion` is a DataFusion session with
the same tables, created on first use. Tables are stored with their doubles as
the model has them (below).

**DataFusion is optional** (`pip install 'sverify[datafusion]'`): it runs plans
with `engine="datafusion"` and compiles SQL strings, and nothing else needs it
(`python/tests/test_without_datafusion.py` blocks its import). It is pinned to
51: Ibis 12's DataFusion backend can't connect to 52 and later. Tables are
registered there as record batches, not datasets: DataFusion pushes filters
into datasets, where PyArrow compares doubles by IEEE rules, which would make
filters and projections disagree on NaN.

#### Doubles: one zero and one NaN

The model has the doubles users expect from SQL (PostgreSQL, DuckDB, Spark,
Snowflake): −0.0 is 0.0, and every NaN is one NaN, equal to itself and above
`inf`. `-1 * 0.0` is `0.0`, `-0.0 >= 0` is TRUE, and `GROUP BY`, `DISTINCT`,
joins, partitions and sorts put the two zeros (and all NaNs) together. Each
engine is made to agree:

* DuckDB, Polars, Snowflake and Spark already compare this way. Their SQL (or
  Polars expressions) makes a table's −0.0 zero on read, and adds `0.0` after
  every operation that IEEE lets produce −0.0 (negation, `*`, `/`, `POWER`,
  rounding, `AVG`): `-0.0 + 0.0` is `0.0`, and other values stay. Ibis
  queries on a connection run on DuckDB, so they agree too.
* DataFusion orders doubles by `f64::total_cmp` (−0.0 < 0.0, a negative NaN
  first), so connections store canonical tables (`sverify.engine.canonical`),
  its results are canonicalized, and the plans Lean writes wrap every double
  operation in `nanvl(x + 0.0, 'NaN')`, which DataFusion evaluates and every
  parser reads back as `x`. Two gaps remain: a `SUM` or `AVG` of doubles
  inside a plan on DataFusion is not wrapped, so a sum that is NaN (as
  `inf + -inf`, negative on x86) or underflows to −0.0, and is then compared
  in the same plan, follows DataFusion's order; and so does SQL run on
  DataFusion directly (`run_sql`, a query on `con.datafusion`).

### The Ibis producer

Ibis expressions become Substrait directly, without SQL:
`sverify/ibis_substrait` is [ibis-substrait](https://github.com/ibis-project/ibis-substrait)
(Apache 2.0, last released for Ibis 9), vendored and ported to Ibis 12. It
writes the functions and encodings the Lean parser reads, and each operation
means what Ibis's own DataFusion SQL compiler makes of it, with Ibis's type
promotions written as explicit casts. That makes plans typed: `qty > amount`
compares as doubles, where DataFusion's producer (from its unanalysed plan)
left an integer next to a double's code (#16). Upstream's mistakes are fixed
(integer `/` divided integers, `where=` filters were dropped, sorts were always
`NULLS FIRST`, promotions could cast a double down to an integer, timestamp
literals were read in local time), and anything outside the model raises
`Unsupported`. `python/tests/test_ibis_substrait.py` checks every verified
coverage case against DataFusion running Ibis's SQL on random tables.

SQL strings still go through DataFusion's producer.

### Engines

Plans come from the Ibis producer or DataFusion's Substrait producer, and they can run on
DuckDB (the default, below), [Polars](https://pola.rs) or DataFusion. Pass
`engine="polars"` to `sv.connect`, `IncrementalView` or
`sv.run_plan(con, plan, "polars")`. The tables stay in `con` and are handed to
the engine as Arrow. The point is differential testing,
with the Lean semantics as the spec.

Polars runs Lean's own serialisation of the checked plan: the plan as
`substrait-check --write` writes it back out from the parsed `Rel`
(`sv.written_plan`), and the delta plans of `--delta`, which use the same
writer. `sverify/polars_engine.py` translates only that small, canonical form
to a `LazyFrame` and raises `Unsupported` on anything else. It does not go
through Ibis's Polars backend, which would compile a different plan. The
translator pins the semantics instead of taking Polars defaults:

* Filters and join conditions keep a row only when it is TRUE. `and`/`or` are
  written out as Kleene `and3`/`or3`. Equi-join keys never match on NULL.
  Semi and anti joins keep the left rows with (without) a TRUE match, so an
  anti join keeps a row whose key is NULL. Lean writes an outer join as a
  left join plus the unmatched right rows (an anti join), padded with NULLs.
* Rows come out in `Rel.eval`'s order. Joins are left-major, with a left
  join's padded row in its place, and windows emit their sorted order. Sorts
  are stable, so ties keep their input order, and `DISTINCT` keeps the first
  of each set of equal rows in place. So `FetchRel` takes the same rows as
  Lean, and the tests compare Polars with Lean row for row.
* Doubles compare, join, partition and sort with one zero and one NaN
  (`-inf < … < 0.0 < … < inf < NaN`), like the float codes. Sorts place NULLs
  as each key says. `DISTINCT` compares rows as `Value`s: NULLs are equal,
  and so are -0.0 and 0.0, and all NaNs.
* Aggregates (`aggregateEval`): one row per group, in order of first
  occurrence (or exactly one without `GROUP BY`), grouping as `DISTINCT`
  compares. Each measure skips NULLs and the rows its `FILTER` drops;
  `DISTINCT` measures keep the first of equal values. Integer `SUM` is exact
  and raises `IntegerOverflow` outside 64 bits, where DataFusion wraps. `SUM`
  and `AVG` of doubles add one by one in Lean's list order.
* Strings are sequences of Unicode scalar values: `character_length`,
  `strpos` and `substring` count characters, not bytes, and `substring` with
  a start below 1 keeps only the positions that exist. `LIKE` escapes with a
  backslash, and a trailing one stands for itself. `UPPER`, `LOWER` and
  regular expressions are black boxes in Lean; Polars computes them with the
  Rust code DataFusion uses.
* `date_part` and `date_trunc` follow `SubstraitLean/Time.lean`: parts
  within a day are integer arithmetic on the microseconds, the calendar comes
  from chrono (as in DataFusion), and `date_part` is NULL outside the years
  chrono represents.
* Integers are unbounded in Lean. Polars computes on 128 bits, and a result
  outside 64 bits raises `IntegerOverflow`, where DataFusion wraps silently
  (`2^62 + 2^62` gives `-2^63`). Integer division and remainder truncate
  toward zero, as `Int.tdiv` and `Int.tmod` do (Polars' own operators floor).
* Runtime errors are the `Issue`s of `SubstraitLean/Safety.lean`: division by
  zero, `MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions
  that do not compile and `date_trunc` to a week or longer outside ±2⁶³ ns. Each expression
  carries a per-row flag for each one, masked by `CASE` as `Expr.issues`
  masks it. The operator raises the matching error if a flag is set on a row
  it evaluates. Polars runs filters where the plan puts them, so a filter
  guards the projections above it. DataFusion merges filters, which is what
  `Rel.loose` models.
* Doubles divide in numpy: Polars divides a column by a constant by
  multiplying with its reciprocal, which rounds differently.

`python/tests/test_polars.py` runs every golden fixture (among them sorts,
`DISTINCT`, semi, anti and outer joins, and the string and time functions),
the window and rewrite queries of the other suites, and every delta plan of
the example pipelines on both engines. It checks Polars against DataFusion as bags and
against Lean's `Rel.eval` in order. It also has targeted tests for NULL join
keys, three-valued filters, NULL and NaN order in windows, overflow, and each runtime error and its guards. The
incremental-view tests run on both engines.

`python/tests/test_backends.py` runs every Ibis operation the coverage
harness verifies on random tables, on DataFusion, Polars and DuckDB, and
generates its Snowflake SQL and runs its Spark SQL on a local Spark session; `test_text.py` and `test_time.py` run their edge
cases on all three engines.

Known gaps: the writer gives virtual tables placeholder `i64` column types and
writes `FetchRel`'s deprecated `offset`/`count`. DataFusion rejects both, so
written plans with string `VALUES` or a fetch run only on Polars. Doubles in a
virtual table come out as their integer codes. `lt` on strings or booleans is
undefined in the model (unlike in SQL), so the translator refuses it.

### DuckDB, through generated SQL

`engine="duckdb"` runs plans on [DuckDB](https://duckdb.org) as SQL that
`sverify.sql.to_sql(plan, DUCKDB)` generates from them. DuckDB's Substrait
extension is not used. Like Polars, DuckDB runs Lean's written plans over the
tables of `con`, which are copied into a fresh in-process database for each
run. Contracts take `engine=` for their runtime checks on data too:

```python
view = sv.IncrementalView(con, PIPELINES["inner_join"], "v", engine="duckdb")

@sv.transform(ensures=[_.amount < 100], on_unproved="runtime", engine="duckdb")
def passthrough(orders): ...
```

The SQL generator (`python/src/sverify/sql/`) reads Substrait JSON as
`Parse.lean` does. It accepts exactly the plans `substrait-check` accepts and
raises `Unsupported` on everything else. It then writes SQL whose result is
`Rel.eval`. The query spells out every semantic choice instead of leaving it to
the engine:

* subqueries name their columns `c0, c1, …`;
* integers are `BIGINT`, and overflow raises (DataFusion wraps around);
* division and remainder truncate; where DataFusion fails at run time
  (division by zero, `MIN / -1`, bad `POWER` or `CAST(double AS BIGINT)`),
  Lean's value is NULL and the SQL raises;
* doubles have one zero and one NaN (`-inf < … < 0.0 < … < inf < NaN`) in
  comparisons, joins, partitions and sorts, and −0.0 is made 0.0 wherever it
  could arise;
* every `ORDER BY` key says `NULLS FIRST`/`LAST`;
* filters keep only TRUE rows; semi and anti joins are `[NOT] EXISTS` over
  the rows where the condition is TRUE;
* `DISTINCT` groups by the same keys as a window partition, so equal means
  equal as `Value`s;
* aggregates group by the same keys as `DISTINCT`; a `DISTINCT` measure
  counts the first row of each value, integer `SUM` raises outside 64 bits,
  and doubles are added in Lean's order (`list_reduce` over a list ordered
  by the ordinal), so the result has Lean's bits, not DataFusion's;
* strings: lengths and positions count characters, a `substring` start below
  1 is handled before it reaches the engine (which would count it from the
  end), and `LIKE` names its escape character;
* `date_part` and `date_trunc` use the engine's calendar functions where they
  agree with `SubstraitLean/Time.lean` (ISO weeks, `dow` from Sunday,
  milliseconds within the minute), and the SQL raises where DataFusion's
  calendar truncation fails;
* below a `FETCH`, a window or a sort, an ordinal column carries Lean's list
  order, so `LIMIT` and ties in sorts and windows pick Lean's rows, and a
  sorted result comes out in Lean's order.

Engine differences go through the hooks of a `Dialect`
(`sverify/sql/core.py`). DuckDB's is `sverify/sql/duckdb.py`.

`python/tests/test_sql.py` checks the generator. Every golden fixture and every
delta plan of the incremental fixtures and example pipelines runs on DataFusion
and on DuckDB with random tables. The results must agree with each other and
with Lean's `Rel.eval` (row for row, in Lean's order, when `FETCH` or a window
makes order matter). The file also has targeted tests for engine traps: NULL
join keys, three-valued logic, NULL ordering in windows, refused integer
division, overflow, and NaN and signed zeros. It keeps snapshots of the
generated SQL in `python/tests/sql_snapshots/`. The incremental, window,
rewrite and ASOF differential tests run on DuckDB too.

#### Snowflake

`to_sql(plan, SNOWFLAKE)` (from `sverify.sql.snowflake`) writes checked plans
and Lean delta plans as Snowflake SQL. The SQL is written to match Lean where
Snowflake's documented behaviour differs:

* integers are `NUMBER(38,0)` and are checked against the 64-bit range;
  division and remainder truncate (through `MOD`, as `/` rounds to six
  decimals), and `CAST(double AS BIGINT)` truncates and raises out of range;
* timestamps are `TIMESTAMP_NTZ(6)`; weeks, days of the week and truncation
  to a week use the ISO functions, not the session's `WEEK_START`;
* backslashes and control characters in strings are escaped;
* every identifier is quoted, so create tables and columns with quoted
  lower-case names.

Where Snowflake can't match, the plan is refused (`Unsupported`) or the query
raises instead of answering differently:

* FETCH over a named table is refused: Snowflake tables have no row order.
  So is a `SUM` or `AVG` of doubles, whose rounding depends on the order of
  the additions.
  Windows and sorts are refused too, unless you pass `tie_free=True` to
  promise there are no ties on their keys (a contract report's
  `deterministic` says so for windows).
* Interval-valued expressions (`ts1 - ts0`) are refused: Snowflake has no
  interval type.

Time columns must be `TIMESTAMP_NTZ`, and string columns must have no
collation. `python/tests/test_sql_snowflake.py` snapshots the SQL for every
fixture and delta plan, parses it with sqlglot's Snowflake parser, and runs it
on [fakesnow](https://github.com/tekumara/fakesnow) against Lean's `Rel.eval`,
along with sorts, `DISTINCT`, aggregates, semi, anti and outer joins and
string functions.
fakesnow emulates Snowflake on DuckDB, so this checks the SQL, not Snowflake's
behaviour. To run the same checks on a real account, set `SNOWFLAKE_ACCOUNT`,
`SNOWFLAKE_USER`, a credential (`SNOWFLAKE_PASSWORD`,
`SNOWFLAKE_AUTHENTICATOR` or `SNOWFLAKE_PRIVATE_KEY_FILE`) and
`SNOWFLAKE_WAREHOUSE`/`DATABASE`/`SCHEMA`.

#### Spark

`to_sql(plan, SPARK)` (from `sverify.sql.spark`) writes checked plans and
Lean delta plans as Spark SQL, for Spark 4 and Databricks SQL. With the
`spark` extra, `sverify.spark_engine.run(plan, tables)` runs a plan over Arrow
tables on a local session (or on the session you pass). Run it in a
session with the settings of `SPARK_CONF`: ANSI mode
(`spark.sql.ansi.enabled`), without which an overflow wraps around and a bad
cast gives NULL, plus a pinned time zone, NTZ timestamps, case-sensitive
names and backslash escapes in string literals. The SQL matches Lean where
Spark differs:

* integers are `BIGINT`; division is `div` (`/` gives a double) and
  remainder `%`, both truncating; a `SUM` adds `DECIMAL(38,0)` values, since
  Spark raises when a partial sum overflows even if the total fits;
* doubles divided by zero give ±inf or NaN (ANSI mode raises);
  `CAST(double AS BIGINT)` is range-checked first (Spark saturates at 2⁶³);
  `FLOOR` and `CEIL` (which return `BIGINT`) keep NaN, ±inf and large values;
* timestamps are `TIMESTAMP_NTZ` and intervals `INTERVAL DAY TO SECOND`;
  `date_trunc` returns a time-zone timestamp, so truncation is computed on
  `TIMESTAMP_NTZ` and `DATE` values;
* backslashes and control characters in strings are escaped, and every
  identifier is quoted with backticks.

Spark refuses, as Snowflake does, FETCH and sorts or windows over a named
table without `tie_free=True` (tables have no row order), and so `SUM` or
`AVG` of doubles over one. It also refuses `POWER` of doubles, which is Java's
`Math.pow` (within 1 ulp of C's).

String columns must use the default `UTF8_BINARY` collation (code point
order). `python/tests/test_sql_spark.py` snapshots the SQL, parses it with
sqlglot's Spark parser, and runs the Snowflake suite's queries, the hooks
and `date_part`/`date_trunc` at the calendar's edges on a local Spark session
against `Rel.eval`; `test_backends.py` runs every coverage case there. The
session needs a JVM (Java 17 or 21: `JAVA_HOME` or `java` on `PATH`), or the
Spark tests are skipped (`poe test-spark` runs them).

**Trusted components** (not covered by the proofs): the JSON parser and
writer, the `sverify` glue (change tables, consolidation, merge), the Polars
translator, the SQL generator, and each engine's execution (DataFusion's
Substrait consumer, Polars, DuckDB's and Spark's SQL). These are covered by golden tests,
round trips and the differential tests instead.

## What's here

| File | Contents |
|---|---|
| `SubstraitLean/Value.lean` | Nullable values, rows, bag-semantics relations |
| `SubstraitLean/Float.lean` | Doubles as exact integer codes (multiples of 2⁻¹⁰⁷⁴), NaN and −0.0 |
| `SubstraitLean/Rounding.lean` | Exact `FLOOR`/`CEIL`/`ROUND` and casts to `BIGINT` on double codes; monotonicity |
| `SubstraitLean/Text.lean` | String functions, `LIKE`; black-box `UPPER`/`LOWER`/regexes; patterns that certainly compile |
| `SubstraitLean/Time.lean` | Exact `date_part` and `date_trunc` on the proleptic Gregorian calendar; monotonicity |
| `SubstraitLean/Expr.lean` | `Literal`, `FieldReference`, scalar functions, `IfThen`, Kleene 3-valued logic |
| `SubstraitLean/Window.lean` | Sort orders, `ROW_NUMBER`/`LAG`/`LEAD` semantics over partitions |
| `SubstraitLean/Aggregate.lean` | `GROUP BY` with `COUNT`/`SUM`/`MIN`/`MAX`/`AVG` (`DISTINCT`, `FILTER`) semantics |
| `SubstraitLean/Rel.lean` | `Read`, `VirtualTable`, `Filter`, `Project`, `Emit`, `Cross`, `Join` (inner/left/semi/anti), `Sort`, `Aggregate`, `Fetch`, `UnionAll`, `Window`; arity, well-formedness, `eval`; **type soundness** |
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
| `SubstraitLean/Safety.lean` | Runtime errors and 64-bit wrap-around; `Rel.mayIssues_sound` |
| `SubstraitLean/Partition.lean` | Sharded evaluation of linear plans, two-phase `COUNT`/`SUM`/`MIN`/`MAX`; `Rel.shardSplit_sound` |
| `SubstraitLean/Guards.lean` | Guard elimination: unchecked engine functions are exact where no issue happens; `Rel.guardFree_sound` |
| `SubstraitLean/ContractCheck.lean` | `--contract`: proving postconditions from preconditions and schemas |
| `SubstraitLean/ShardCheck.lean` | `--shard`: splitting a plan into per-shard and combining plans (trusted) |
| `SubstraitLean/Check.lean` | Executable `checkWF`, proven equivalent to `Rel.WF`; `Decidable` instance |
| `SubstraitLean/Parse.lean` | Substrait protobuf-JSON → `Rel` (trusted) |
| `SubstraitLean/Pretty.lean` | Plan / row rendering |
| `Main.lean` | `substrait-check` CLI (`--delta` for engine delta plans) |
| `python/` | `sverify`: contracts, incremental views, pipelines, Delta/Iceberg IO, sharding; the DuckDB, Polars, DataFusion and Spark runners and the Snowflake SQL; differential tests |
| `notebooks/` | The tour: 16 marimo chapters |
| `tests/` | Golden tests of the CLI (`tests/run.sh`, plans in `tests/fixtures`) |
| `docs/optimizations.md` | Proved optimizations beyond incremental maintenance: what engines already do, what is proved, what is next |
| `catalogue/` | 139 real analytical queries (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O, practitioner, IoT and finance idioms), probed against the checker and the engines; [`FINDINGS.md`](catalogue/FINDINGS.md) |
| `SubstraitLean/Examples.lean` | Concrete plans checked with `#guard` at build time, plus `#print axioms` |

### Proven theorems

* `Rel.eval_arity`: a well-formed plan on a well-formed catalog only produces
  rows of its declared arity.
* `filter_filter`: `Filter(Filter(r,p),q) = Filter(r, p AND q)`, which also holds under three-valued logic.
* `filter_true`, `fetch_zero_none`: identity eliminations.
* `filter_unionAll`: filter distributes over `UNION ALL`.
* `unionAll_comm`: `UNION ALL` commutes up to bag equivalence (`≈ᵣ`).
* `join_inner_eq_filter_cross`: an inner join is a filtered cross product.
* `filter_project_pushdown`: a filter that only reads input columns can be moved below a `ProjectRel`.
* `filter_cross_pushdown_left`: a filter that only reads left columns can be pushed into the left side of a `CrossRel`.
* `emit_project_identity`: emitting only the input columns of a `ProjectRel` removes the projection.
* `Rel.eval_sharded`, `twoPhase_correct`, `Rel.shardSplit_sound`: a plan linear in the sharded
  tables is the union of its results on the shards (with split keys, also aggregates grouped by
  the key and `DISTINCT` over it), and decomposable aggregates combine in two phases
  ([docs/optimizations.md](docs/optimizations.md)).
* `Rel.evalI_eq`, `Rel.guardFree_sound`: a plan whose only possible issues are integer `SUM`s
  runs correctly without per-row checks.

### Contracts

[Contracts.lean](SubstraitLean/Contracts.lean) is an abstract interpreter
over `Rel`. Each column gets an `AVal`, a set of possible values: whether it can be NULL, an integer
interval, possible booleans, and whether it can be a string.

* `Expr.abs_sound`: abstract evaluation of expressions is sound, including SQL's
  three-valued `AND`/`OR`, NULL-propagating arithmetic and comparisons.
* `Expr.refine_sound`: a row that passes a filter satisfies what the condition
  says about its columns.
* `Expr.factsOf_sound`, `Rel.facts_sound`: relational facts (`x − y ∈ [lo, hi]`,
  `x ≠ k`) taken from filter and join conditions hold on every output row. They
  survive projections, emits, joins, NULL padding and unions.
* `Expr.absD_sound`: evaluating expressions with those facts (sharpening
  `x − y`, `x < y`, `x = y` and `x = k`) is sound. Each `CASE` branch is
  evaluated knowing whether its condition is TRUE: `Expr.cstr_sound` turns
  `IS NULL` and comparisons with constants into constraints on the tested
  expression (or its negation), and `Expr.refineNeg_sound` refines columns
  where a condition is not TRUE. This is how `clip`, `abs`, `greatest` and
  `least` get their bounds. `Expr.refine_sound` also covers `OR`, so a filter
  `x IN (1, 2, 3)` gives `x ∈ [1, 3]`.
* `Rel.keys_sound` ([Keys.lean](SubstraitLean/Keys.lean)): derived keys hold. No two
  output rows agree on them.
* Key rules for ASOF (all in `Rel.keys_sound`): `ROW_NUMBER()` with the partition
  columns is a key (`windowRows_rowNumber_key`); a column `$i + c` of a non-NULL
  integer column can stand in for it in a key; a filter `$i = k` drops `i` from
  keys; join keys drop right-key columns the condition ties to the left side
  (`a.device = b.device`), for inner and left joins.
* `window_tiebreak`, `Rel.window_deterministic` ([Keys.lean](SubstraitLean/Keys.lean)):
  when a window's partition and sort columns contain a key of its input, every
  arrangement of the input sorted by the window's keys gives the same rows as
  `Rel.eval`. So the proofs describe what DataFusion computes, however it breaks ties.
* `orderFact_sound`, `winFacts_sound`, `WinFn.abs_sound`: what is known about
  `LAG`/`LEAD`/`ROW_NUMBER` columns holds. Strict order uses an oracle saying
  which windows have a key (`WindowKeys`); `Rel.keyedWindows_sound` proves the
  one computed from `Rel.keys` right, which is what `contract_sound` asks for.
* `IoT.window_complete` ([Completeness.lean](SubstraitLean/Completeness.lean)): the
  converse of the contracts. If both sensors have valid readings at `t` and `t + 60`,
  the window at `t` is in the output, so no window is lost. It's built from one
  membership lemma per operator.

Doubles are modelled as exact integer codes (each double is a multiple of 2⁻¹⁰⁷⁴),
timestamps as microseconds; see [Float.lean](SubstraitLean/Float.lean). The conversions
between codes and native floats are trusted code.
* `Rel.aeval_sound`: every row a well-formed plan produces is described by `Rel.aeval`.
* `Rel.colExprs_eval`: a precondition plan (`orders.select(cond, ...)`) computes its
  conditions row by row, so "all its columns are TRUE" is the precondition.
* `contract_sound`: suppose every input row matches its schema and satisfies its
  preconditions. If every column of the postcondition plan is certainly TRUE,
  then every output row satisfies every postcondition.

Trusted: the schema description taken from `baseSchema` types and nullability, and
the JSON plumbing.

### Composition

[Compose.lean](SubstraitLean/Compose.lean) builds on `contract_sound`,
`Rel.keys_sound` and `Rel.delta_correct`, with no induction over plans:

* `Triple.compose`: Hoare triples over queries compose, `{P} g {Q}` and
  `{Q} f {S}` give `{P} f ∘ g {S}`, where `f ∘ g` reads `g`'s output as one of
  its tables. `Triple.of_contract`, `Triple.of_keys` and `Triple.of_aeval` turn
  what the checker proves into triples; `Triple.compose_spec` is the rule as
  `sverify` applies it.
* `RowsSat.update`, `KeyOn.update`, `Spec.update`: a table's contract survives a
  batch if the inserted rows satisfy the row conditions and their keys clash
  with neither each other nor the kept rows. `Triple.maintained`: a contracted
  view's guarantees then hold in the new state.
* `Rel.chain_sound`: when a view reads another view's materialized result and
  gets that view's delta-plan output as its change table, its own delta plan is
  correct (DBSP's chain rule). `Rel.stack_sound` holds for any upstream change;
  `ZSet.diff_correct` shows a recomputed view's `new − old` is one.

### Runtime errors

[Safety.lean](SubstraitLean/Safety.lean) proves that a transformation runs without
runtime errors, or reports what may go wrong. `sverify` reports these as
`may fail: …` (a `VerificationError` from `@sv.transform`) or, for wrapping,
`warning: …`.

* Errors, where DataFusion fails: integer division or remainder by zero, `MIN / -1`,
  integer `POWER` with a negative exponent or a result outside 64 bits,
  `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, a regular expression
  that may not compile, and `date_trunc` to a week, month, quarter or year outside
  ±2⁶³ nanoseconds (DataFusion panics or returns garbage there).
* Warnings: `+`, `-`, `*` and negation leaving 64 bits, an integer `SUM` (nothing
  bounds how many rows a group has), and `date_trunc` to a day or
  less below `-2⁶³` µs. DataFusion wraps around silently, so the result is not the
  mathematical one.
* `Rel.mayIssues_sound`: every issue that can happen on any input is reported. Guards
  are understood where DataFusion respects them: in a `CASE` branch (and so
  `NULLIF(b, 0)`), or in a filter below a *projection*. They are not respected in the
  same `AND`, nor in an earlier *filter*: DataFusion merges filters, so
  `t.filter(n != 0).filter(q % n > 1)` can fail.
* `FloatCode.floor_mono`, `round_mono`, `toInt?_mono`, `toInt?_of_range`
  ([Rounding.lean](SubstraitLean/Rounding.lean)): `FLOOR`, `CEIL`, `ROUND` and the cast
  to `BIGINT` are exact on double codes and monotone, so `amount ∈ [0, 100]` proves
  `amount.round()` is an integer in `[0, 100]`, and the cast safe.
* Abstract rules for truncating `/` and `%` (`divBound_sound`, `modBound_sound`) and
  for squares (`powAbs_sound`).
* `Time.monthIndex_spec`, `Time.trunc_mono`, `Time.year_mono`
  ([Time.lean](SubstraitLean/Time.lean)): every day lies in the month the calendar
  arithmetic computes, so years and truncations grow with the timestamp, and
  `ts ∈ [2024-01-01, 2025-01-01)` proves `ts.year() == 2024` and
  `ts.truncate("M") >= 2024-01-01`. The other parts have proved ranges (`day` in
  `[1, 31]`, …); `date_part` is `NULL` outside the years ±262142.

Trusted: *when* DataFusion evaluates an expression (`Rel.HasIssue`: `CASE` is lazy,
`AND`/`OR` are not, filter and join conditions may run before the filters below
them). `python/tests/test_numeric.py` runs DataFusion on random data and checks it
only fails where an error was reported. `BIGINT` and timestamp columns are taken to
hold 64-bit values (from the schema); arithmetic on 32-bit columns is checked
against 64-bit limits, so its overflow is not caught.

### Incremental view maintenance

Table updates are Z-sets: rows with signed weights, where a deletion has weight `-1` and an
update is a delete plus an insert. This follows DBSP (Budiu et al., VLDB 2023).
It covers every operator except left, semi and anti joins, `DISTINCT`, aggregates,
fetch and windows (`Rel.Incremental`):

* `Rel.zeval_add`: `Q(D + ΔD) ~ Q(D) + ΔQ`. Filter, project, emit, sort and union
  are linear (a sort only orders the bag), and cross and inner join use the bilinear rule
  `Δ(A×B) = ΔA×(B+ΔB) + A×ΔB`.
* `Rel.delta`: compiles a plan into a **delta plan**, an ordinary `Rel` that reads the
  old tables and the change tables (`δ t`, e.g. `orders$delta`).
  `Rel.delta_correct` proves it computes exactly `ΔQ`.
* `Rel.incremental_sound`: combines the two, so old result + delta-plan output =
  full recomputation.
* `Rel.zeval_lift`: with all weights 1, Z-set evaluation equals the bag
  semantics `Rel.eval`, so the two models agree.
* `Rel.zeval_terms`: a plan's result is the concatenation of its union-free
  terms' results (`Rel.terms`).
* `Rel.weighted_eval`: running the weight-column encoding (`Rel.weighted`) on an
  ordinary bag engine gives exactly the Z-set result, with each weight as a
  trailing column. Old tables get weight 1, and joins multiply weights.

Equivalence is `List.Perm`, which never cancels `+1` against `-1`. That makes it
stronger than Z-set equality, so the results also hold under consolidation.
`Examples.lean` runs a delete, an insert and an update through a filter/project
plan and an inner join where both sides change.

### Table formats

[TableFormat.lean](SubstraitLean/TableFormat.lean) covers what `sverify.io`
takes from Delta Lake and Iceberg, with the format's part as explicit
hypotheses:

* `Rel.zeval_weight_congr`: on the incremental fragment, Z-set evaluation only
  depends on the tables' weights. A change feed deletes and re-inserts rows,
  so the old table plus the feed is not a permutation of the new table, only
  equal in weights.
* `Rel.cdf_sound`: if the feed turns each old snapshot into the new one up to
  weights (`ChangeFeed`, trusted) and is loaded as the change tables (`hδ` of
  `Rel.delta_correct`), the old view plus the delta plan's output has the
  weights of the view on the new snapshot. `ChangeFeed.of_diff`: the diff of
  two snapshots is such a feed, so the fallback needs no trust in the feed.
* `stats_table`: with correct per-file statistics (`ColStats.Correct`,
  trusted), every row of the table lies in the join of the files' bounds;
  `stats_append`: the files an append added bound its rows; `stats_bounds`:
  that bound is the `IS NOT NULL AND c >= lo AND c <= hi` fact handed to the
  contract checker.

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Modelling choices

* **Positional schemas.** Substrait field references are ordinals, so a
  schema is just an arity. Types beyond "nullable value" are not tracked yet.
* **Project appends, Emit narrows.** This matches Substrait's `ProjectRel` +
  `RelCommon.emit`. Here `Emit` is its own node rather than a field on every rel.
* **Bags as lists.** `Rel.eval` returns a `List`, and plan equivalence is `List.Perm`.
  Several rewrites are stronger than that and hold as exact list equality.
* **Windows sort stably.** `Rel.eval` sorts a window's input with a stable merge
  sort, so ties keep input order. The checker only claims results for windows
  without ties (see `window_tiebreak`).
* **Fetch is order-dependent.** Without a `SortRel`, real engines may return any
  rows. The semantics fixes list order, so `fetch` theorems describe one valid behavior.
  `SortRel` is a stable sort here, while engines may order ties either way, so after
  `ORDER BY … LIMIT` the checker's claims hold for every row the engine could keep.
* **Semi joins and `DISTINCT` are their own operators.** `Rel.semi` keeps the left
  rows with some (or, for anti joins, no) matching right row; `Rel.distinct` keeps
  the first occurrence of every row (NULLs equal, doubles by their codes: one
  zero and one NaN). `DISTINCT` rows are a key (`Rel.keys`). DataFusion writes
  `DISTINCT` as an aggregate with one empty grouping, which its own consumer
  rejects; the parser reads it as "all columns".
* **Aggregates have one grouping set.** `Rel.aggregate` outputs one row per
  distinct grouping value (NULLs group together; doubles by their codes, so
  -0.0 and 0.0 are one group), or exactly one row without
  grouping expressions, even on an empty input. Measures skip NULLs; on no
  values `COUNT` is 0 and the rest are NULL. Integer `SUM` is exact (DataFusion
  wraps around, which is a warning), double `SUM`/`AVG` add with native floats
  (DataFusion promises no order; contracts only say "a double"), and `AVG` of
  integers is the `AVG` of their conversion to double. `MIN`/`MAX` of doubles
  are refused: DataFusion's grouped version turns a group of +∞ into the largest
  finite double and skips NaN next to other values. The grouping columns are a
  key of the result.
* **Ill-typed calls evaluate to `null`.** This keeps `eval` total. `Rel.WF` rules out
  out-of-range field references.
* **Some operations are rewrites in the parser.** `IN` lists become `OR`s of
  equalities; `COALESCE`, `NULLIF`, `GREATEST`, `LEAST` and `ABS` become
  conditionals; `RIGHT JOIN` becomes a `LEFT JOIN` with its sides swapped;
  `FULL OUTER JOIN` becomes the left join plus the anti join of the right side,
  padded with NULLs; `x IN (subquery)` in a filter becomes a semi join on `=`;
  `UNION` is `DISTINCT` of `UNION ALL`; `IS NOT DISTINCT FROM` becomes a
  conditional. The rewrites are trusted code, checked against DataFusion by
  `python/tests/test_rewrites.py` and `python/tests/test_relations.py`. (`ABS` of the smallest `BIGINT` fails in
  DataFusion; here it is reported as wrapping around.)
* **Integers are unbounded; overflow is an `Issue`.** `Rel.eval` computes exact
  integers, and [Safety.lean](SubstraitLean/Safety.lean) reports every operation that may
  leave 64 bits. Where DataFusion fails instead (division, `POWER`, casts), the
  value in the model is `NULL`.
* **Strings are Unicode scalar values.** `substring`, `strpos`, `LIKE`, `btrim`, `||`
  and `character_length` are computed exactly, checked against DataFusion by
  `python/tests/test_text.py`. `UPPER`, `LOWER` and regular expressions are black
  boxes (`opaque`): no proof depends on what they compute, and Lean's evaluator
  handles only ASCII case and no regular expressions. A pattern is an error unless
  `Text.simpleRegex` accepts it, a conservative subset of Rust's syntax that is
  tested to compile.
* **Timestamps are microseconds (UTC).** `date_part` and `date_trunc` are computed
  exactly, checked against DataFusion by `python/tests/test_time.py`, including at
  the ends of the ranges where DataFusion stops being exact. Dates (`DATE`) are not
  supported by them yet.
* **Integer `//` from Ibis is exact.** Ibis compiles it through doubles
  (`CAST(FLOOR(CAST(a AS DOUBLE) / b) AS BIGINT)`), which is wrong beyond 2⁵³;
  `sverify` compiles it to integer division instead.

## Prior work to build on

No existing formal semantics for Substrait came up in my search. The closest work formalizes SQL or relational algebra:

**Coq (most mature)**
* **SQLCert / SQL_Coq** (Benzaken, Contejean): a mechanized semantics for
  realistic SQL with nulls, aggregates and correlated subqueries, an extended bag
  algebra, and proofs of common optimizer rewrites.
  [HAL 01487062](https://hal.archives-ouvertes.fr/hal-01487062),
  [HAL 01955433](https://hal.archives-ouvertes.fr/hal-01955433)
* **HoTTSQL** (Chu, Weitz, Cheung, Suciu; PLDI 2017): denotes queries as
  K-relations using univalence. It proves many rewrite rules, and the Cosette prover grew out of it.
  [arXiv 1607.04822](https://arxiv.org/abs/1607.04822),
  [PLDI page](https://pldi17.sigplan.org/event/pldi-2017-papers-hottsql-proving-query-rewrites-with-univalent-sql-semantics)
* **A Formalization of SQL with Nulls** (Ricciotti, Cheney; JAR 2022): covers
  three-valued logic, set and bag operations, lateral joins and nested subqueries.
  [arXiv 2003.11331](https://arxiv.org/abs/2003.11331),
  [PMC9637088](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC9637088/)
* **Q\*cert** (Auerbach et al., SIGMOD 2017): a verified query compiler
  built around the nested relational algebra (NRA<sup>e</sup>). It's the closest
  analogue to "verified IR for queries".

**Lean 4**
* **RelationalAlgebra** (Rickerd): relational algebra ≡ first-order logic, built on Mathlib.
  [Reservoir](https://reservoir.lean-lang.org/@Rickerd1234/RelationalAlgebra)
* **provenance** (Senellart): semantics for ProvSQL with semiring provenance,
  a natural route to K-relation semantics in Lean.
  [Reservoir](https://reservoir.lean-lang.org/@PierreSenellart/provenance)
* Emergence AI's [Lean SQL equivalence write-up](https://www.emergence.ai/blog/formal-verification-of-sql-queries-in-lean-for-enhanced-accuracy)
  and the typed-queries chapter of
  [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Worked-Example___-Typed-Queries/).

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

1. **Non-linear incremental operators.** Aggregates (SUM and COUNT per group
   are linear over Z-sets), `DISTINCT`, semi and left joins, windows.
2. **Completeness.** Contracts say what every output row satisfies; the
   converse ("no window is lost") is a Lean theorem per plan today
   (`IoT.window_complete`), not something the checker reports.
3. **Translation validation.** Given a plan and its optimized form, have Lean
   check that they are equivalent. A decision procedure for the conjunctive
   fragment would mirror Cosette and HoTTSQL.
4. **Real types.** A typing judgement over Substrait types (decimals, dates,
   nullability), with `eval` proven to respect it.
5. **Mathlib `Multiset` or K-relations.** Move bag equivalence to quotients, or
   generalize to semiring-annotated relations as HoTTSQL and provenance do.
