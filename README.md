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

**New to formal verification?** The [marimo notebook](notebooks/intro.py) is an
interactive introduction with live examples. [notebooks/fitness.py](notebooks/fitness.py)
is one realistic pipeline end to end: heart-rate samples joined with workouts,
a decorator contract with proved and refused postconditions, and an
incrementally maintained view you can stream samples into (see [Setup](#setup)
for how to open them).

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
uv run pytest                    # should end with "56 passed"
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
| `poe lint` | `ruff check` and `ruff format --check` |
| `poe fmt` | Fixes lint issues and formats the Python code |
| `poe typecheck` | Type-checks the Python code with pyrefly |
| `poe golden` | Golden tests: CLI output on every plan in `tests/fixtures` |
| `poe test` | Python tests, including the randomized engine tests |

From the project root, use `uv run --project python poe -C python qa`. The Lean
tasks need `lake` on your PATH.

### The notebooks

```bash
uvx marimo run --sandbox notebooks/intro.py      # read-only app view
```
```bash
uvx marimo run --sandbox notebooks/fitness.py    # the fitness pipeline
```
```bash
uv run --project python --with marimo marimo edit notebooks/intro.py   # edit it
```

With the second command, marimo asks whether to run in a sandboxed venv.
Answer **n** to use the project's environment, so cells can `import sverify`.
Answer **Y** to get a sandbox with only the notebook's own dependencies, which
is enough for the introduction.

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
# NotIncremental: not incrementally maintainable (left join, fetch or window)

totals = orders.group_by("customer").aggregate(total=orders.amount.sum())
sv.IncrementalView(con, totals, "totals")
# ValueError: ... unsupported relation: {"aggregate": ...
```

Aggregates (`GROUP BY` with `SUM`/`COUNT`) are the next thing to add; see
[Possible next steps](#possible-next-steps).

How much of the Ibis API gets through, from
[`sverify/coverage.py`](python/src/sverify/coverage.py) (regenerate with
`uv run python -m sverify.coverage --write-readme` in `python/`):

<!-- coverage:start -->
32 of 82 probed Ibis operations reach the checker (✓ verified, ✗ rejected by the checker, – fails in Ibis or DataFusion; *inc.* marks incremental maintenance).

| Area | Operations |
|---|---|
| rows | ✓ filter, select *inc.* · ✓ mutate *inc.* · ✓ drop, rename *inc.* · ✓ drop_null *inc.* · ✓ isnull *inc.* · ✓ between *inc.* · ✓ isin *inc.* · ✓ notin *inc.* · ✓ ifelse *inc.* · ✓ cases *inc.* · ✗ order_by · ✓ limit · ✓ limit with offset · ✗ order_by + limit · ✗ sample |
| joins | ✓ inner join *inc.* · ✓ non-equi join *inc.* · ✓ cross join *inc.* · ✓ left join · ✓ right join · ✗ outer join · ✗ semi join · ✗ anti join · ✗ isin subquery · ✓ union all *inc.* · ✗ union distinct · ✗ intersect · ✗ difference |
| aggregation | ✗ count() · ✗ group_by sum · ✗ count, max, mean · ✗ nunique · ✗ sum(where=) · ✗ having · ✗ value_counts · ✗ distinct · ✗ distinct(on=) · ✗ std · ✗ collect · – scalar subquery · – unnest |
| windows | ✓ row_number · ✓ lag · ✗ rank · ✗ dense_rank · ✗ cumsum · ✗ sum over group · ✗ rolling mean (rows) · – rolling mean (interval) · ✗ ntile · ✗ first |
| numbers | ✓ +, -, * *inc.* · ✓ float division *inc.* · ✗ integer division · ✗ mod · ✓ abs *inc.* · ✗ round · ✗ ceil, floor · ✗ power · ✓ greatest *inc.* · ✓ least *inc.* · ✓ clip *inc.* · ✓ cast int → double *inc.* · ✗ cast int → string · ✗ cast double → int |
| nulls | ✓ fill_null *inc.* · ✓ coalesce *inc.* · ✓ nullif *inc.* |
| strings | ✗ upper · ✗ length · ✗ concat · ✗ substr · ✗ contains · ✗ startswith · ✗ like · ✗ re_search · ✗ strip |
| time | ✓ timestamp + interval *inc.* · ✓ compare with literal *inc.* · ✗ year · ✗ date · ✗ truncate |
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

  [notebooks/fitness.py](notebooks/fitness.py) walks through a complete example.

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

### Engines

Plans always come from DataFusion's Substrait producer (and from Lean, for
delta plans). Where they run is chosen per call, with `engine=`:

```python
view = sv.IncrementalView(con, PIPELINES["inner_join"], "v", engine="duckdb")

@sv.transform(ensures=[_.amount < 100], on_unproved="runtime", engine="duckdb")
def passthrough(orders): ...
```

* **DataFusion** (the default) runs plans with its own Substrait consumer, on
  `con`'s tables.
* **DuckDB** runs them as SQL that `sverify.sql.to_sql(plan, DUCKDB)` generates
  from the plan. DuckDB's Substrait extension is not used. Tables are copied
  into an in-process DuckDB database, and base-table changes go to both.

The SQL generator (`python/src/sverify/sql/`) reads Substrait JSON as
`Parse.lean` does. It accepts exactly the plans `substrait-check` accepts and
raises `Unsupported` on everything else. It then writes SQL whose result is
`Rel.eval`. The query spells out every semantic choice instead of leaving it to
the engine:

* subqueries name their columns `c0, c1, …`;
* integers are `BIGINT`, and overflow raises (DataFusion wraps around);
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
rewrite and ASOF differential tests run on both engines.

**Engine notes.** DataFusion 51 is pinned: Ibis 12's DataFusion backend can't
connect to 52 and later. Ibis's `create_table` is broken on DataFusion, so
`sverify` registers Arrow tables directly (`sv.create_table`). They are
registered as record batches, not datasets: DataFusion pushes filters into
datasets, where PyArrow compares doubles by IEEE rules instead of DataFusion's
total order, which would make filters and projections disagree on NaN.

**Trusted components** (not covered by the proofs): the JSON parser and
writer, the `sverify` glue (change tables, consolidation, merge), the SQL
generator, and the engines' execution (DataFusion's Substrait consumer,
DuckDB's SQL). These are covered by golden tests, round trips and the
differential tests instead.

## What's here

| File | Contents |
|---|---|
| `SubstraitLean/Value.lean` | Nullable values, rows, bag-semantics relations |
| `SubstraitLean/Expr.lean` | `Literal`, `FieldReference`, scalar functions, `IfThen`, Kleene 3-valued logic |
| `SubstraitLean/Window.lean` | Sort orders, `ROW_NUMBER`/`LAG`/`LEAD` semantics over partitions |
| `SubstraitLean/Rel.lean` | `Read`, `VirtualTable`, `Filter`, `Project`, `Emit`, `Cross`, `Join` (inner/left), `Fetch`, `UnionAll`, `Window`; arity, well-formedness, `eval`; **type soundness** |
| `SubstraitLean/Rewrites.lean` | Verified rewrites (below) |
| `SubstraitLean/Incremental.lean` | Z-set semantics, delta rules, delta plans (incremental view maintenance) |
| `SubstraitLean/Terms.lean` | Splitting a plan into union-free terms (for DataFusion's consumer) |
| `SubstraitLean/Weighted.lean` | Weight-column encoding for bag engines; `isIncremental` |
| `SubstraitLean/Write.lean` | `Rel` → Substrait JSON, delta plans for engines (trusted) |
| `SubstraitLean/Contracts.lean` | Verified abstract interpreter: NULLs, intervals, filter refinement; `contract_sound` |
| `SubstraitLean/ContractCheck.lean` | `--contract`: proving postconditions from preconditions and schemas |
| `SubstraitLean/Check.lean` | Executable `checkWF`, proven equivalent to `Rel.WF`; `Decidable` instance |
| `SubstraitLean/Parse.lean` | Substrait protobuf-JSON → `Rel` (trusted) |
| `SubstraitLean/Pretty.lean` | Plan / row rendering |
| `Main.lean` | `substrait-check` CLI (`--delta` for engine delta plans) |
| `python/` | `sverify`: contracts and incremental views on DataFusion, differential tests |
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

### Incremental view maintenance

Table updates are Z-sets: rows with signed weights, where a deletion has weight `-1` and an
update is a delete plus an insert. This follows DBSP (Budiu et al., VLDB 2023).
It covers every operator except left join and fetch (`Rel.Incremental`):

* `Rel.zeval_add`: `Q(D + ΔD) ~ Q(D) + ΔQ`. Filter, project, emit and union are
  linear, and cross and inner join use the bilinear rule
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
* **Ill-typed calls evaluate to `null`.** This keeps `eval` total. `Rel.WF` rules out
  out-of-range field references.
* **Some operations are rewrites in the parser.** `IN` lists become `OR`s of
  equalities; `COALESCE`, `NULLIF`, `GREATEST`, `LEAST` and `ABS` become
  conditionals; `RIGHT JOIN` becomes a `LEFT JOIN` with its sides swapped.
  The rewrites are trusted code, checked against DataFusion by
  `python/tests/test_rewrites.py`. Integers are unbounded, so 64-bit overflow
  (e.g. `ABS` of the smallest `BIGINT`) is not modelled yet.

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
1. **Non-linear operators.** Aggregates (SUM/COUNT per group are linear over
   Z-sets), DISTINCT and left join. Real plans use `AggregateRel` a lot.
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
