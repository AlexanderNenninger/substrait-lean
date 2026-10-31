# substrait-lean

**Keep query results up to date without recomputing them, with updates proven correct.**

Say you have a dashboard table built from a join over a few million orders, and
a hundred orders change every hour. Recomputing the whole join each time is
slow. Hand-written incremental logic ("only process rows where `updated_at` is
newer than…") is fast, but it tends to go wrong silently: deletes are missed,
late rows are skipped, a join gets a new match.

This project gives you a third option. You write the query once, in Ibis or SQL,
and `sverify` maintains the result in DataFusion from the inserts and deletes alone.
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
engine-neutral format for query plans. [DataFusion](https://datafusion.apache.org)
writes your query as a Substrait plan, Lean checks it and computes the proven
update plan, and DataFusion runs that plan.

**New here?** [The tour](notebooks/00_start_here.py) is a series of interactive
[marimo](https://marimo.io) notebooks, one per feature, that you can work through
in order: plans and proofs, the checker, contracts, keys, doubles and time,
runtime errors, windows and ASOF joins, composition, incremental views,
pipelines, engines, a complete pipeline end to end, and what exactly is
proved. No prior knowledge of formal verification or data engineering is
assumed. See [The tour](#the-tour) for how to open it.

## Setup

You need [uv](https://docs.astral.sh/uv/) for Python and
[elan](https://github.com/leanprover/elan) for Lean (elan is to Lean what
rustup is to Rust, or uv to Python):

```bash
brew install uv          # or: curl -LsSf https://astral.sh/uv/install.sh | sh
```
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Open a new terminal so `lake` (Lean's build tool) is on your PATH. Then, from
the project root:

```bash
lake build                       # checks every proof and builds the substrait-check CLI
```
```bash
cd python && uv sync             # DataFusion 51, DuckDB, Ibis, pyarrow, substrait, pytest, hypothesis
```
```bash
uv run pytest                    # should end with "161 passed"
```

`uv sync` installs `sverify` in editable mode. Its build hook runs
`lake build substrait-check` and links `sverify/_bin/substrait-check` to the
result, so later `lake build`s take effect without reinstalling. To use a
different binary, set `SVERIFY_CHECK` to its path.

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
| `poe test` | Python tests, including the randomized engine tests |
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
| 11 | [Engines and SQL](notebooks/11_engines.py) | DataFusion, Polars, DuckDB; SQL for DuckDB and Snowflake |
| 12 | [A complete pipeline](notebooks/12_fitness.py) | heart rate during workouts, end to end |
| 13 | [What is proved, what is trusted](notebooks/13_trust.py) | the trusted boundary, a glossary and a map of the code |
| 14 | [DataFusion's surprising semantics](notebooks/14_datafusion_semantics.py) | appendix: every DataFusion quirk, checked against the Lean model |

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

con = sv.connect()  # an Ibis DataFusion backend
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
| aggregation | ✓ count() · ✓ group_by sum · ✓ count, max, mean · ✓ nunique · ✓ sum(where=) · ✓ having · ✓ value_counts · ✓ distinct · ✗ distinct(on=) · ✗ std · ✗ collect · – scalar subquery · – unnest |
| windows | ✓ row_number · ✓ lag · ✗ rank · ✗ dense_rank · ✗ cumsum · ✗ sum over group · ✗ rolling mean (rows) · – rolling mean (interval) · ✗ ntile · ✗ first |
| numbers | ✓ +, -, * *inc.* · ✓ float division *inc.* · ✓ integer division *inc.* · ✓ mod *inc.* · ✓ abs *inc.* · ✓ round *inc.* · ✓ ceil, floor *inc.* · ✓ power *inc.* · ✓ greatest *inc.* · ✓ least *inc.* · ✓ clip *inc.* · ✓ cast int → double *inc.* · ✓ cast int → string *inc.* · ✓ cast double → int *inc.* |
| nulls | ✓ fill_null *inc.* · ✓ coalesce *inc.* · ✓ nullif *inc.* |
| strings | ✓ upper *inc.* · ✓ length *inc.* · ✓ concat *inc.* · ✓ substr *inc.* · ✓ contains *inc.* · ✓ startswith *inc.* · ✓ like *inc.* · ✓ re_search *inc.* · ✓ strip *inc.* |
| time | ✓ timestamp + interval *inc.* · ✓ compare with literal *inc.* · ✓ year *inc.* · ✓ date *inc.* · ✓ truncate *inc.* |
<!-- coverage:end -->

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
  isn't modelled. Comparisons follow DataFusion's total order: NaN equals itself
  and sorts above every number (so `v > 0` keeps NaN rows), and −0.0 < +0.0.
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
produced by DataFusion's Substrait producer (Substrait 0.77). It then:

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
DataFusion, using delta plans from Lean:

```python
import sverify as sv
from sverify.examples import PIPELINES, create_tables

con = sv.connect()          # an Ibis DataFusion backend
create_tables(con, orders_rows=[(1, "ada", 30)], customers_rows=[("ada", "Paris")])
view = sv.IncrementalView(con, PIPELINES["inner_join"], "v")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 7)], deletes=[(1, "ada", 30)]),
            "customers": sv.Changes(inserts=[("bob", "Rome")])})
assert view.rows() == view.recompute()
```

The query can be an Ibis expression or a SQL string.

How it works:

1. Ibis writes the query as DataFusion SQL, and DataFusion's Substrait producer
   turns it into a plan.
2. `substrait-check --delta` compiles the plan with `Rel.delta`, splits it into
   union-free terms (`Rel.terms`) and applies the weight-column encoding
   (`Rel.weighted`). It prints one Substrait plan per term, after checking each
   one is incremental and well-formed. The plans are union-free because
   DataFusion's Substrait consumer loses table qualifiers at a `UNION ALL`,
   and the duplicate column names then break a later join.
3. For each change batch, `sverify` registers the change tables `t$delta` (rows
   plus `__weight` = ±1), runs every term with DataFusion's Substrait consumer,
   sums the weights per row, and merges the result into the view.

`python/tests/test_incremental.py` is a differential test (with `hypothesis`):
after random insert/delete batches, the maintained view must equal the query
recomputed from scratch. It runs every pipeline in `sverify/examples.py`:
filters and projections, inner joins, self-joins, `UNION ALL`, cross products,
and a filter-join-compute chain. It also runs one plain-SQL query, so the SQL
entry point stays covered.

**Engine notes.** DataFusion 51 is pinned: Ibis 12's DataFusion backend can't
connect to 52 and later. Ibis's `create_table` is broken on DataFusion, so
`sverify` registers Arrow tables directly (`sv.create_table`). They are
registered as record batches, not datasets: DataFusion pushes filters into
datasets, where PyArrow compares doubles by IEEE rules instead of DataFusion's
total order, which would make filters and projections disagree on NaN.

### Engines

Plans always come from DataFusion's Substrait producer, but they can run on
DataFusion, [Polars](https://pola.rs) or DuckDB (below). Pass `engine="polars"` to
`IncrementalView` or `sv.run_plan(con, plan, "polars")`. The tables stay in
`con` and are handed to Polars as Arrow. The point is differential testing,
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
* Rows come out in `Rel.eval`'s order. Joins are left-major, with a left
  join's padded row in its place, and windows emit their sorted order. So
  `FetchRel` takes the same rows as Lean, and the tests compare Polars with
  Lean row for row.
* Doubles compare, join, partition and sort by DataFusion's total order
  (`-NaN < -inf < … < -0.0 < +0.0 < … < inf < NaN`), like the float codes.
  Window sorts are stable and place NULLs as each key says.
* Integers are unbounded in Lean. Polars computes on 128 bits, and a result
  outside 64 bits raises `IntegerOverflow`, where DataFusion wraps silently
  (`2^62 + 2^62` gives `-2^63`). Integer division and remainder truncate
  toward zero, as `Int.tdiv` and `Int.tmod` do (Polars' own operators floor).
* Runtime errors are the `Issue`s of `SubstraitLean/Safety.lean`: division by
  zero, `MIN / -1`, bad `POWER`s and out-of-range casts. Each expression
  carries a per-row flag for each one, masked by `CASE` as `Expr.issues`
  masks it. The operator raises the matching error if a flag is set on a row
  it evaluates. Polars runs filters where the plan puts them, so a filter
  guards the projections above it. DataFusion merges filters, which is what
  `Rel.loose` models.
* Doubles divide in numpy: Polars divides a column by a constant by
  multiplying with its reciprocal, which rounds differently.

`python/tests/test_polars.py` runs every golden fixture, the window and
rewrite queries of the other suites, and every delta plan of the example
pipelines on both engines. It checks Polars against DataFusion as bags and
against Lean's `Rel.eval` in order. It also has targeted tests for NULL join
keys, three-valued filters, NULL and NaN order in windows, overflow, and each runtime error and its guards. The
incremental-view tests run on both engines.

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
* doubles compare by the model's total order (`-NaN < -inf < … < -0.0 < +0.0
  < … < inf < NaN`) in comparisons, joins, partitions and sorts;
* every `ORDER BY` key says `NULLS FIRST`/`LAST`;
* filters keep only TRUE rows;
* below a `FETCH` or a window, an ordinal column carries Lean's list order, so
  `LIMIT` and window ties pick Lean's rows.

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
* timestamps are `TIMESTAMP_NTZ(6)`;
* backslashes in strings are escaped;
* every identifier is quoted, so create tables and columns with quoted
  lower-case names.

Where Snowflake can't match, the plan is refused (`Unsupported`) or the query
raises instead of answering differently:

* FETCH over a named table is refused: Snowflake tables have no row order.
  Windows are refused too, unless you pass `tie_free=True` to promise there
  are no ties (a contract report's `deterministic` says so).
* Interval-valued expressions (`ts1 - ts0`) are refused: Snowflake has no
  interval type.
* Snowflake has one NaN, which stands for Lean's +NaN. A negative-NaN literal
  is refused, and negating a NaN raises.
* Lean orders −0.0 below +0.0, and Snowflake doesn't document whether the sign
  of a zero is visible. So comparing two zeros raises, and so does sorting or
  partitioning on a double column that holds a zero.

Time columns must be `TIMESTAMP_NTZ`, and string columns must have no
collation. `python/tests/test_sql_snowflake.py` snapshots the SQL for every
fixture and delta plan, parses it with sqlglot's Snowflake parser, and runs it
on [fakesnow](https://github.com/tekumara/fakesnow) against Lean's `Rel.eval`.
fakesnow emulates Snowflake on DuckDB, so this checks the SQL, not Snowflake's
behaviour. To run the same checks on a real account, set `SNOWFLAKE_ACCOUNT`,
`SNOWFLAKE_USER`, a credential (`SNOWFLAKE_PASSWORD`,
`SNOWFLAKE_AUTHENTICATOR` or `SNOWFLAKE_PRIVATE_KEY_FILE`) and
`SNOWFLAKE_WAREHOUSE`/`DATABASE`/`SCHEMA`.

**Trusted components** (not covered by the proofs): the JSON parser and
writer, the `sverify` glue (change tables, consolidation, merge), the Polars
translator, the SQL generator, and each engine's execution (DataFusion's
Substrait consumer, Polars, DuckDB's SQL). These are covered by golden tests,
round trips and the differential tests instead.

## What's here

| File | Contents |
|---|---|
| `SubstraitLean/Value.lean` | Nullable values, rows, bag-semantics relations |
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
| `SubstraitLean/Compose.lean` | Composing contracts (Hoare triples), preconditions under updates, views over views (chain rule) |
| `SubstraitLean/Safety.lean` | Runtime errors and 64-bit wrap-around; `Rel.mayIssues_sound` |
| `SubstraitLean/ContractCheck.lean` | `--contract`: proving postconditions from preconditions and schemas |
| `SubstraitLean/Check.lean` | Executable `checkWF`, proven equivalent to `Rel.WF`; `Decidable` instance |
| `SubstraitLean/Parse.lean` | Substrait protobuf-JSON → `Rel` (trusted) |
| `SubstraitLean/Pretty.lean` | Plan / row rendering |
| `Main.lean` | `substrait-check` CLI (`--delta` for engine delta plans) |
| `python/` | `sverify`: contracts and incremental views on DataFusion or Polars, differential tests |
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
  the first occurrence of every row (NULLs equal, doubles by their codes, as in
  DataFusion). `DISTINCT` rows are a key (`Rel.keys`). DataFusion writes
  `DISTINCT` as an aggregate with one empty grouping, which its own consumer
  rejects; the parser reads it as "all columns".
* **Aggregates have one grouping set.** `Rel.aggregate` outputs one row per
  distinct grouping value (NULLs group together; doubles by their codes, so
  -0.0 and 0.0 are two groups, as in DataFusion), or exactly one row without
  grouping expressions, even on an empty input. Measures skip NULLs; on no
  values `COUNT` is 0 and the rest are NULL. Integer `SUM` is exact (DataFusion
  wraps around, which is a warning), double `SUM`/`AVG` add with native floats
  (DataFusion promises no order; contracts only say "a double"), and `AVG` of
  integers is the `AVG` of their conversion to double. `MIN`/`MAX` of doubles
  are refused: DataFusion's grouped version turns a group of +∞ into the largest
  finite double, skips NaN next to other values, and lets the row order pick
  between -0.0 and 0.0. The grouping columns are a key of the result.
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

0. **Completeness for ASOF and windows.** Contracts say what every output row
   satisfies; the converse ("every accelerometer sample with a gyroscope sample
   within 10 ms is matched") is a Lean theorem per plan today
   (`IoT.window_complete`), not something the checker reports. Still missing for
   windows: framed aggregates (`AVG(v) OVER (ROWS 5 PRECEDING)`) and
   incremental maintenance.
1. **Non-linear operators.** Incremental aggregates (SUM/COUNT per group are
   linear over Z-sets), DISTINCT, semi and left joins; grouping sets, `STDDEV`
   and `ARRAY_AGG`.
2. **Translation validation.** Given a plan and its optimized form, have Lean
   check that they are equivalent. A decision procedure for the conjunctive
   fragment would mirror Cosette and HoTTSQL.
3. **Real types.** Add a typing judgement over Substrait types (integer overflow,
   decimals, nullability) and prove `eval` respects it.
4. **Mathlib `Multiset` or K-relations.** Move bag equivalence to quotients, or
   generalize to semiring-annotated relations as HoTTSQL and provenance do.
5. **Compare the Lean evaluator with the engine.** The differential tests
   compare incremental and full evaluation, both on DataFusion. For windows and
   ASOF joins, `sverify.testing` already runs Lean's `eval` against DataFusion on
   generated tables; the other operators could get the same.
