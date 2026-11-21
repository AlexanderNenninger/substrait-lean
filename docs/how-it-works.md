# How it works

How plans are checked, how the engines are made to agree, and exactly what
is proved. The user-facing side is in [getting-started.md](getting-started.md) and [tasks.md](tasks.md); the map of the
proofs, with each module's job and the theorems each guarantee rests
on, is in [proofs.md](proofs.md).

```python
import ibis
import sverify as sv
from ibis import _

con = sv.connect()
con.create("orders", ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
           [(2, "bob", 5), (3, "cy", 50)])
```

```bash
# skip: builds or tests the repository, which needs elan and takes minutes
lake build                                                  # proofs + CLI
tests/run.sh                                                # golden tests for the CLI
```

The core package depends on Lean core alone. Mathlib is used only by the separate [`float-bounds/`](float-bounds.md) project.

## Checking real plans

`substrait-check` reads any Substrait JSON plan, shows it in readable form,
and reports what was proved about it:

```python
from sverify.engines.plan import substrait_json

plan = substrait_json(con, "select id, amount * 2 as doubled from orders where amount > 10")
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

`substrait-check plan.json` reads a Substrait plan in protobuf-JSON form, as
produced by `sverify`'s Ibis producer or its SQL lift, or by another
Substrait producer (Substrait 0.77). It then:

1. translates it into the formal `Rel` model, or rejects anything outside the fragment (exit 1);
2. decides whether the plan is well formed (a decision the proofs show equals the formal one,
   [proved-theorems.md](proved-theorems.md)), and checks that the root's output names match the
   output arity (exit 2 if ill-formed);
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

What it accepts is the model's fragment (the operators are listed in
[`core/Sverify/Core/Rel.lean`](../core/Sverify/Core/Rel.lean)): the coverage table under [What is supported](../README.md#ibis-coverage)
probes it from the Ibis side, and the catalogue's
[`features.toml`](../catalogue/features.toml) records it per feature. Function
calls are matched by name in `extensions`, and anything else is rejected.

The CLI also reports whether the plan is in the incremental fragment
(`isIncremental`, which the proofs show equals the formal definition) and whether writing
it back out as JSON and re-parsing gives the same plan (`roundtrip: ok`).

The parser ([Parse.lean](../frontend/Sverify/Frontend/Parse.lean)) and writer
([Write.lean](../frontend/Sverify/Frontend/Write.lean)) are trusted, unproved code. The
proofs are about `Rel`, so a parser bug would make the CLI check the wrong plan.
The golden tests in `tests/fixtures` are the guard against that. The
`df_*.json` fixtures are real plans that DataFusion's Substrait producer wrote
for the Ibis pipelines in `sverify_dev/examples.py`, kept as static golden
inputs ([`tests/fixtures/README.md`](../tests/fixtures/README.md)). The others are
hand-written.

## How incremental views work

`python/` holds `sverify`, which maintains query results incrementally on
DuckDB (by default) or Polars, using delta plans
from Lean. A
node's `refresh` runs an incremental view (`sverify.incremental`, internal):

```python
import ibis
import sverify as sv
from sverify.incremental import IncrementalView
from sverify.io import Changes

con = sv.connect()          # Arrow tables; plans run on DuckDB
orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
customers = ibis.table({"name": "string", "city": "string"}, name="customers")
con.create("orders", orders.schema(), [(1, "ada", 30)])
con.create("customers", customers.schema(), [("ada", "Paris")])
query = orders.join(customers, orders.customer == customers.name).select(orders.id, customers.city)
view = IncrementalView(con, query, "v")
view.apply({"orders": Changes(inserts=[(3, "bob", 7)], deletes=[(1, "ada", 30)]),
            "customers": Changes(inserts=[("bob", "Rome")])})
assert view.rows() == view.recompute()
```

The query can be an Ibis expression or a SQL string. A node's view reads its
sources, or the stored nodes it reads, as the view's base tables.

How it works:

1. The query becomes a Substrait plan: an Ibis expression through the vendored
   Ibis producer (below), a SQL string through sverify's own lift (see "SQL
   producers" below).
2. `substrait-check --delta` compiles the plan into its delta plan and applies the
   weight-column encoding. It prints one Substrait plan, after
   checking it is incremental and well-formed.
3. For each change batch, `sverify` registers the change tables `t$delta` (rows
   plus `__weight` = ±1), runs the delta plan on the connection's engine
   (DuckDB by default) as one query, sums the weights per row, and merges the
   result into the view. A k-way join's delta plan is one `UNION ALL` of its
   2^k − 1 terms.

`python/tests/test_incremental.py` is a differential test (with `hypothesis`):
after random insert/delete batches, the maintained view must equal the query
recomputed from scratch. It runs every pipeline in `sverify_dev/examples.py`:
filters and projections, inner joins, self-joins, `UNION ALL`, cross products,
and a filter-join-compute chain. It also runs one plain-SQL query, so the SQL
entry point stays covered.

Connections. `sv.connect(engine=...)` gives a `Connection`: the Arrow
tables (`con.create`, `con.put`, `con.get`), the engine plans run on, and Ibis
tables bound to them (`con.table(name)`, through an in-memory Ibis DuckDB
backend that views the Arrow tables, so Ibis's own `.to_pyarrow()` works and
contracts find a table's data). Tables are stored with their doubles as
the reference profile reads them (below).

A Delta or Iceberg source on DuckDB is held as a scan (`sverify._scan.Scan`):
the data files sverify keeps after its own pruning, the rows that deletion
vectors or position delete files remove (by file and row position), the
schema and the source's filter. DuckDB reads it as a view over
`read_parquet`, and the Ibis backend views the same files, so the table never
passes through Python. Columns are cast to the types DuckDB gives the Arrow
schema, a column no file has is NULL, and doubles are read as the reference
profile has them, which also keeps DuckDB from trusting Parquet's NaN-free statistics
([`upstream/bugs/DD-4.json`](../upstream/bugs/DD-4.json)). Reading a scan as Arrow (`con.rows`, an engine other than DuckDB) reads it into
Arrow, which is how the other engines get it. A refresh holds the table as the
files of the new version, after DuckDB checks that the batch's deletes are in
the old files. If those files were vacuumed, the views reading the table are
recomputed on the new snapshot. `python/tests/test_io_native.py` compares
both paths at every version and through refreshes.

An incremental view's state is a weighted table: its rows, each once, with
their number of copies (`sverify._weighted`). On DuckDB, DuckDB holds it
between refreshes (`sverify._state.DuckDBStore`, a `Resident` table in the
process's one DuckDB database, which the engine and every connection's Ibis
backend share), and the view's rows are a DuckDB view of it. On Polars and
Spark it is a list of Parquet parts that the engine writes and reads
(`sverify._parts`). Either way, states and changes are added up by
one plan Lean checks: the union of two weighted tables, grouped by every
column, with the weights summed and the groups of weight 0 left out
(`sverify._state.Merger`). Each engine's lowering groups rows as the reference
compares them, so the merge gives the same state on every engine
(`python/tests/test_state.py` runs it on each).

On DuckDB, a refresh changes a view's state in place, at the cost of the
change (`DuckDBStore.apply`). It looks up the state rows equal to a row of
the change (a null-safe equality join on the canonical values), adds the
change to them with the merge plan, and replaces them, for every view in one
DuckDB transaction, so a failed commit changes no view. The state still
holds each row once with its weight. A view whose new contents are read
before the commit, by a view recomputed on the new tables or by the audit,
is merged in full. Each view keeps a log of its changes for the sinks that
have not written them yet, and a sink writes their sum
(`IncrementalView.changes_since`), so no old state is kept.

On Polars and Spark, a refresh writes the change as a new part and leaves
the state's other parts where they are, so the state stays out of the Python
process (#1329). Sverify adds the parts up, with the same merge plan, when
something reads the table (the view's rows, a sink, `rows()`), when a change
deletes a row, and when the rows added since the last sum are as many as the
sum holds or there are more than 16 parts, so the files on disk stay within
about twice the added-up state. A refresh that only inserts costs the change.
On Polars, with a state of 2 or 8 million rows, inserting 100,000 rows takes
0.1 s at either size, a refresh that deletes a row takes 0.4 s and 1.6 s, and
the first read of the table after four inserts takes 0.2 s and 0.5 s
([#1712](https://github.com/AlexanderNenninger/substrait-lean/pull/1712)).
On Spark each change is a Spark job that writes Parquet, so a refresh costs
more than it did while the state sat in the driver: four inserts of a quarter
of the rows each into a filter view take about 2.9 times as long on a local
session (17.3 s against 6.0 s for 2 million rows), and the driver peaks at
525 MB where it peaked at 708 MB, and at 1104 MB where it peaked at 1849 MB
for 8 million rows
([#1680](https://github.com/AlexanderNenninger/substrait-lean/pull/1680)). On
Spark, inserting 100,000 rows into a built state takes 1.0 s at 2 or 8
million rows, a refresh that deletes a row takes 2.8 s and 9.3 s, and the
first read of the table after four inserts takes 2.9 s and 10.1 s. On both
engines, a read after every refresh and a refresh that deletes a row pay the
merge over the whole state each time.
`SVERIFY_STATE_LOCATION` names where the parts live: a directory, or a URI
that the driver and every executor read and write
([Environment variables](tasks.md#environment-variables)).

A node on DuckDB has DuckDB write its Delta and Iceberg sinks
(`sverify.io._engine`). DuckDB writes the Parquet files of the state or of
the change, cast to the sink's schema. It finds where the rows a change
deletes are by joining the sink's scan, with each row's file and position,
to the deleted rows by the model's row equality, one position per deleted
copy. sverify then commits the files: for Delta, add and remove actions in
one transaction (the files holding deleted rows are rewritten without them)
with statistics as delta-rs writes them and the transaction `(app_id,
epoch)`; for Iceberg, a data file with the table's field ids and a position
delete file, in one snapshot. Readers of the sink's change feed see the
rewritten files as deleted and added, which nets to the change.
`python/tests/test_io_engine_sinks.py` writes the same nodes through DuckDB
and through delta-rs and pyiceberg, and compares the tables after every
refresh and the statistics both record.

Other engines read what the sinks write (#861).
`python/tests/test_io_sink_readers.py` writes a merged, a maintained and a
replaced table in each format. delta-rs, pyiceberg, DuckDB's `delta_scan`
and `iceberg_scan`, and sverify's own sources each read the rows the writes
call for, and the contract record survives each library's own maintenance.
`python/tests/test_delta_dat.py` reads the Delta Acceptance Testing suite
through `DeltaSource`. Spark's own readers are outside these tests: sverify
pins pyspark 4.3, and on Maven Central (2026-11-21) the newest delta-spark,
4.4.1, builds against Spark 4.2, and the newest iceberg-spark-runtime,
1.12.0, against Spark 4.1
([#2140](https://github.com/AlexanderNenninger/substrait-lean/issues/2140)).

#### Doubles under the reference profile

The core has IEEE's doubles, both zeros and signed NaNs, and each profile
chooses how to read them
([core, profiles and engines](core-and-profiles.md)).
The reference profile reads them as users expect from SQL (PostgreSQL,
DuckDB, Spark, Snowflake): −0.0 is 0.0, and every NaN is one NaN, equal to
itself and above `inf` (`ONE_ZERO`, `ONE_NAN`, `NAN_IS_NAN`, NaN `GREATEST`). `-1 * 0.0` is `0.0`, `-0.0 >= 0` is TRUE, and `GROUP BY`, `DISTINCT`,
joins, partitions and sorts put the two zeros (and all NaNs) together. Each
engine is made to agree:

* DuckDB, Polars, Snowflake and Spark already compare this way. Their SQL (or
  Polars expressions) makes a table's −0.0 zero on read, and adds `0.0` after
  every operation that IEEE lets produce −0.0 (negation, `*`, `/`, `POWER`,
  rounding, `AVG`): `-0.0 + 0.0` is `0.0`, and other values stay. Ibis
  queries on a connection run on DuckDB, so they agree too.
* `Report.to_substrait` writes each double operation `x` for other consumers
  as `if is_nan(x + 0.0) then NaN else x + 0.0` (ST-4), which gives every NaN
  the same sign and payload.

### The Ibis producer

Ibis expressions become Substrait directly, without SQL:
`sverify/ibis_substrait` is [ibis-substrait](https://github.com/ibis-project/ibis-substrait)
(Apache 2.0, last released for Ibis 9), vendored and ported to Ibis 12. It
writes the functions and encodings the Lean parser reads, and each operation
means what [the Ibis frontend](reference-semantics.md#the-ibis-frontend) says, with Ibis's
type promotions written as explicit casts. That makes plans typed: `qty >
amount` compares as doubles. Upstream's mistakes are fixed
(integer `/` divided integers, `where=` filters were dropped, sorts were always
`NULLS FIRST`, promotions could cast a double down to an integer, timestamp
literals were read in local time), and anything outside the model raises
`UnsupportedError`. `python/tests/test_ibis_substrait.py` checks every proved
coverage case against DuckDB running Ibis's own SQL on random tables, except
where DuckDB's SQL computes something else (`coverage.NO_DUCKDB_SQL`).

A few operations have no node of their own. Memtables and `ibis.literal(…).as_table()`
become virtual tables, table-level `fill_null` a `COALESCE` per column (as Ibis
rewrites it), and a sort by an expression projects the key, sorts and drops it.
SQL strings (`t.alias("v").sql(…)`) are compiled by sverify's SQL lift and
spliced in, with reads of the alias replaced by its plan.
`INTERSECT ALL` and `EXCEPT ALL` number the copies of each row
(`ROW_NUMBER() OVER (PARTITION BY` every column`)`) and semi- or anti-join on the
rows and their numbers, which keeps min(m, n) or max(m − n, 0) copies: SQL's
meaning, as DuckDB computes it. Ibis writes a `LIMIT`
that is not an integer as a subquery over the table, which is refused.

Subqueries: a correlated `[NOT] EXISTS` in a filter becomes a semi (anti) join
on the subquery's condition; other correlated
subqueries are refused. Uncorrelated ones go into the plan as Substrait
subquery expressions, which the checker lifts into joins (`liftSubquery` in
`frontend/Sverify/Frontend/Parse.lean`): a scalar subquery is a left join on `TRUE`, and
the checker accepts it only where the derived keys prove at most one row (an aggregate without groups,
`LIMIT 1`); `x IN (subquery)` outside a filter's conjuncts is a left join with
the subquery's distinct values plus a count of its `NULL`s, which gives SQL's
three-valued answer; `EXISTS` compares a `COUNT(*)` with 0.

### The SQL lift

SQL strings are DuckDB's SQL, and go through sverify's own lift
(`sverify.sql_lift`): SQLGlot parses the query and resolves its names against
the input tables, and the lift writes a Substrait plan in which every choice
DuckDB's SQL leaves implicit is explicit (casts, output types, function
options, sort directions). It reads a subset of SQL and refuses the
rest.

The parser also reads encodings other producers write: typed function names
(`add:date_iday`), CHAR and VARCHAR literals, window functions inside
expressions (`ROW_NUMBER() OVER (…) - 1`, hoisted into a window), `is_true`
and timestamps at precision 0. It checks the argument kinds a signature names.

### Engines

Plans come from the Ibis producer or sverify's SQL lift, and run on DuckDB
(the default), [Polars](https://pola.rs) or Spark
([the engines](stability.md#engines)). You pick
one with `engine="polars"` on `node.refresh`, `sv.connect` or
`sverify.engines.run(con, plan, "polars")`. The tables stay in `con` and are
handed to the engine as Arrow. Contracts take `engine=` for their runtime
checks on data too:

```python
view = IncrementalView(con, query, "v", engine="duckdb")

@sv.transform(ensures=[_.amount < 100], on_unproved="check", check_engine="duckdb")
def passthrough(orders): ...
```

Each engine's translation, what it pins, how it is tested and its known gaps
are in [engine-profiles.md](engine-profiles.md#the-translations-today).

The parser and writer, the glue, the translators, each engine's execution
and the size hypothesis are trusted, and covered by golden tests, round trips
and the differential tests: [proofs.md, What is trusted](proofs.md#what-is-trusted)
lists each.

## How the results are checked

* Proofs: `lake build` re-checks every theorem. The main ones say that the
  update plan computes exactly the change to the result, and that running it
  with the weight-column encoding gives that result. See
  [Proved theorems](proved-theorems.md).
* Randomized testing: `uv run pytest` generates random tables and random batches of
  inserts and deletes, including NULLs and duplicates. After every batch it
  checks that the maintained result equals a full recompute. This covers the parts
  the proofs don't: the JSON translation, the Python glue and the engine itself.

## What is proved

[Proved theorems](proved-theorems.md) lists what `lake build` re-checks for each guarantee: contracts,
composition, runtime errors, incremental view maintenance and table formats. [proofs.md](proofs.md)
maps each guarantee to its module.

## Where an engine evaluates an expression

A runtime error depends on which rows an engine evaluates an expression on,
and engines evaluate more than the plan says. Sverify assumes that a filter or
join condition may run on its input's rows before the filters below it, that
`AND`, `OR` and `COALESCE` evaluate every argument, and that a `CASE`
evaluates a branch only on the rows that take it. It also assumes that each
part of a condition that always runs may run on the rows of the join inputs
it reads alone, even when another input is empty, as DuckDB's filter pushdown
and hash joins do (#1484). These assumptions are stated in
[`Safety.lean`](../analysis/Sverify/Analysis/Safety.lean)'s header, and
the checker proves that every issue they allow on every order of the ties is
reported ([proved-theorems.md](proved-theorems.md#runtime-errors)).

## Modelling choices

How the Lean model represents and evaluates a plan (positional schemas,
bags as lists, the parser's rewrites, overflow, strings, elementary
functions and time) is in
[reference-semantics.md](reference-semantics.md#how-the-model-holds-a-plan).

## Prior work to build on

[prior-work.md](prior-work.md) credits the work sverify builds on, the formal
semantics of SQL in Coq and Lean among it, and compares sverify with related
tools.
