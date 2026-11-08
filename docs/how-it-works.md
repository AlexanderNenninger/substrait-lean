# How it works

How plans are checked, how the engines are made to agree, and exactly what
is proved. The user-facing side is in [guide.md](guide.md); the map of the
proofs, with each Lean module's job and the theorems each guarantee rests
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
lake build                                                  # proofs + CLI
tests/run.sh                                                # golden tests for the CLI
```

There are no dependencies beyond Lean core (no Mathlib yet), so the build takes seconds.

## Checking real plans

`substrait-check` reads any Substrait JSON plan, shows it in readable form,
and reports what was verified about it:

```python
from sverify.engines import substrait_json

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
Substrait producer such as DataFusion's (Substrait 0.77). It then:

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

What it accepts is the model's fragment (`SubstraitLean/Rel.lean` lists the
operators): the coverage table under [What is supported](../README.md#what-is-supported)
probes it from the Ibis side, and the catalogue's
[`features.toml`](../catalogue/features.toml) records it per feature. Function
calls are matched by name in `extensions`, and anything else is rejected.

The CLI also reports whether the plan is in the incremental fragment
(`isIncremental`, proven equivalent to `Rel.Incremental`) and whether writing
it back out as JSON and re-parsing gives the same `Rel` (`roundtrip: ok`).

The parser ([Parse.lean](../SubstraitLean/Parse.lean)) and writer
([Write.lean](../SubstraitLean/Write.lean)) are trusted, unverified code. The
proofs are about `Rel`, so a parser bug would make the CLI check the wrong plan.
The golden tests in `tests/fixtures` are the guard against that. The
`df_*.json` fixtures are real plans that DataFusion's Substrait producer wrote
for the Ibis pipelines in `sverify_dev/examples.py`, kept as static golden
inputs since sverify stopped planning SQL with DataFusion
([`tests/fixtures/README.md`](../tests/fixtures/README.md)). The others are
hand-written.

## How incremental views work

`python/` holds `sverify`, which maintains query results incrementally on
DuckDB (by default), Polars or the optional DataFusion, using delta plans
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
recomputed from scratch. It runs every pipeline in `sverify_dev/examples.py`:
filters and projections, inner joins, self-joins, `UNION ALL`, cross products,
and a filter-join-compute chain. It also runs one plain-SQL query, so the SQL
entry point stays covered.

Connections. `sv.connect(engine=...)` gives a `Connection`: the Arrow
tables (`con.create`, `con.put`, `con.get`), the engine plans run on, and Ibis
tables bound to them (`con.table(name)`, through an in-memory Ibis DuckDB
backend that views the Arrow tables, so Ibis's own `.to_pyarrow()` works and
contracts find a table's data). The DataFusion engine runs on a private
DataFusion session with the same tables, created on first use. Tables are stored with their doubles as
the model has them (below).

A Delta or Iceberg source on DuckDB is held as a scan (`sverify._scan.Scan`):
the data files sverify keeps after its own pruning, the rows that deletion
vectors or position delete files remove (by file and row position), the
schema and the source's filter. DuckDB reads it as a view over
`read_parquet`, and the Ibis backend views the same files, so the table never
passes through Python. Columns are cast to the types DuckDB gives the Arrow
schema, a column no file has is NULL, and doubles are read as the model has
them, which also keeps DuckDB from trusting Parquet's NaN-free statistics
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
backend share), and the view's rows are a DuckDB view of it. On the other
engines it is an Arrow table. Either way, states and changes are added up by
one plan Lean checks: the union of two weighted tables, grouped by every
column, with the weights summed and the groups of weight 0 left out
(`sverify._state.Merger`). Each engine's lowering groups rows as the model
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

DataFusion is optional (`pip install 'sverify[datafusion]'`): it runs plans
with `engine="datafusion"`, and nothing else needs it
(`python/tests/test_without_datafusion.py` blocks its import). It is pinned to
51: Ibis 12's DataFusion backend can't connect to 52 and later. Tables are
registered there as record batches. DataFusion pushes filters into
datasets, where PyArrow compares doubles by IEEE rules, which would make
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
  parser reads back as `x`. This also gives every NaN the same payload, which
  `total_cmp` would tell apart. Two gaps remain: a `SUM` or `AVG` of doubles
  inside a plan on DataFusion is not wrapped, so a sum that is NaN (as
  `inf + -inf`, negative on x86) or underflows to −0.0, and is then compared
  in the same plan, follows DataFusion's order; and so does SQL run on
  DataFusion directly (a query on a `datafusion.SessionContext`).

### The Ibis producer

Ibis expressions become Substrait directly, without SQL:
`sverify/ibis_substrait` is [ibis-substrait](https://github.com/ibis-project/ibis-substrait)
(Apache 2.0, last released for Ibis 9), vendored and ported to Ibis 12. It
writes the functions and encodings the Lean parser reads, and each operation
means what [the Ibis frontend](reference-semantics.md#the-ibis-frontend) says, with Ibis's
type promotions written as explicit casts. That makes plans typed: `qty >
amount` compares as doubles, where DataFusion's producer (from its unanalysed
plan) once left an integer next to a double's code (#16). Upstream's mistakes are fixed
(integer `/` divided integers, `where=` filters were dropped, sorts were always
`NULLS FIRST`, promotions could cast a double down to an integer, timestamp
literals were read in local time), and anything outside the model raises
`UnsupportedError`. `python/tests/test_ibis_substrait.py` checks every verified
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
meaning, as DuckDB computes it (DataFusion 51's own SQL plans them as a plain
semi and anti join, keeping or dropping every copy). Ibis writes a `LIMIT`
that is not an integer as a subquery over the table, which is refused.

Subqueries: a correlated `[NOT] EXISTS` in a filter becomes a semi (anti) join
on the subquery's condition, as DataFusion decorrelates it; other correlated
subqueries are refused. Uncorrelated ones go into the plan as Substrait
subquery expressions, which the checker lifts into joins (`liftSubquery` in
`SubstraitLean/Parse.lean`): a scalar subquery is a left join on `TRUE`, and
because DataFusion fails when one returns several rows, the checker accepts it
only where `Rel.keys` proves at most one row (an aggregate without groups,
`LIMIT 1`); `x IN (subquery)` outside a filter's conjuncts is a left join with
the subquery's distinct values plus a count of its `NULL`s, which gives SQL's
three-valued answer; `EXISTS` compares a `COUNT(*)` with 0. (DataFusion 51's
own SQL cannot run `IN` or `EXISTS` subqueries in a projection, and its
`NOT IN (subquery)` ignores the subquery's `NULL`s.)

### The SQL lift

SQL strings are DuckDB's SQL, and go through sverify's own lift
(`sverify.sql_lift`): SQLGlot parses the query and resolves its names against
the input tables, and the lift writes a Substrait plan in which every choice
DuckDB's SQL leaves implicit is explicit (casts, output types, function
options, sort directions). It reads a subset of SQL so far and refuses the
rest ([#231](https://github.com/AlexanderNenninger/substrait-lean/issues/231),
[#240](https://github.com/AlexanderNenninger/substrait-lean/issues/240)).

The parser also reads encodings other producers write: typed function names
(`add:date_iday`), CHAR and VARCHAR literals, window functions inside
expressions (`ROW_NUMBER() OVER (…) - 1`, hoisted into `Rel.window`), `is_true`
and timestamps at precision 0. It checks the argument kinds a signature names.

### Engines

Plans come from the Ibis producer or sverify's SQL lift, and run on DuckDB
(the default), [Polars](https://pola.rs) or Spark
([the engines](stability.md#engines)); DataFusion is experimental. You pick
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
  [Proven theorems](#proven-theorems).
* Randomized testing: `uv run pytest` generates random tables and random batches of
  inserts and deletes, including NULLs and duplicates. After every batch it
  checks that the maintained result equals a full recompute. This covers the parts
  the proofs don't: the JSON translation, the Python glue and the engine itself.

## What is proved

### Proven theorems

[proofs.md](proofs.md#the-guarantees-and-their-theorems) names every
guarantee with its theorem, its layer and its module, from the algebraic
rewrites (`filter_filter`, `Rewrites.lean`) to sharding (`Rel.eval_sharded`),
guard elimination (`Rel.guardFree_sound`) and postconditions on every
allowed result (`contract_sound_allowed`). The sections below explain the
main ones.

### Contracts

[Contracts.lean](../SubstraitLean/Contracts.lean) is an abstract interpreter
over `Rel`. Each column gets an `AVal`, a set of possible values: whether it can be NULL, an integer
interval, possible booleans, and whether it can be a string, with the strings
it can be when they are few: at most `strCap` (64) of them, past that any string
(#708).

* `Expr.abs_sound`: abstract evaluation of expressions is sound, including SQL's
  three-valued `AND`/`OR`, NULL-propagating arithmetic and comparisons.
* `Expr.refine_sound`: a row that passes a filter satisfies what the condition
  says about its columns.
* `Expr.factsOf_sound`, `Rel.facts_sound`: relational facts (`x − y ∈ [lo, hi]`,
  `x ≠ k`) taken from filter and join conditions hold on every output row. They
  survive projections, emits, joins, NULL padding and unions.
  A fact `holds e` keeps a whole condition, a conjunct of a precondition or
  of a filter or inner join condition (`Expr.conjuncts_sound`): projections
  rename its columns (`Expr.eval_mapFields`), and a left join drops those of
  its right side, which NULL padding may break (#597).
* `Expr.refineOr_sound`, `useFacts_sound`: a row on which `p OR q` is TRUE,
  and `p` cannot be TRUE under the columns' description, has `q` TRUE, so
  `q` refines the columns; a `CASE` whose condition is decided is its branch.
  `Rel.aeval` applies the whole conditions at each table and filter, and
  `Expr.absD` in each `CASE` branch and on the right of each `OR`.
  `Expr.absF_sound`: a projected condition that is a `holds` fact is TRUE.
* `Expr.absD_sound`: evaluating expressions with those facts (sharpening
  `x − y`, `x < y`, `x = y` and `x = k`) is sound. Each `CASE` branch is
  evaluated knowing whether its condition is TRUE: `Expr.cstr_sound` turns
  `IS NULL` and comparisons with constants into constraints on the tested
  expression (or its negation), and `Expr.refineNeg_sound` refines columns
  where a condition is not TRUE. This is how `clip`, `abs`, `greatest` and
  `least` get their bounds. `Expr.refine_sound` also covers `OR` and
  `IS NULL`, so a filter `x IN (1, 2, 3)` gives `x ∈ [1, 3]` and
  `x IS NULL OR x >= 0` gives "NULL or ≥ 0". `p OR q` is evaluated with `q`
  refined where `p` is not TRUE, also when `p` may be NULL (`orSplitNull`),
  which proves `x >= 0 OR x IS NULL` for a nullable `x`.
  A string constant is that one string, `s = 'k'` and `s IN ('a', 'b')`
  narrow a column to those strings, `s <> 'k'` and `NOT IN` take them out,
  and `CASE`, `COALESCE` and `UNION ALL` join the sets (`AVal.strs`, #708),
  so a filter `status <> 'cancelled'` over a source whose `status` is one of
  four strings proves `status IN ('placed', 'shipped', 'returned')`.
* `Rel.keys_sound` ([Keys.lean](../SubstraitLean/Keys.lean)): derived keys hold. No two
  output rows agree on them.
* `Rel.optimize_sound` ([Semantic.lean](../SubstraitLean/Semantic.lean)): the
  rewrites a contract's keys and facts allow keep a plan's rows, on data that
  meets the preconditions. A `DISTINCT` or measure-less `GROUP BY` over a key
  goes, and so does the `DISTINCT` of `COUNT(DISTINCT id)` with `id` a key.
  A filter the preconditions imply goes; one they rule out empties the plan.
  A left join on a NOT NULL foreign key (`sv.references`) becomes an inner
  join, and so does one under a filter that rejects its padded rows. A join
  whose condition hits a key of the right side goes when nothing reads the
  right side's columns (for an inner join, given a NOT NULL foreign key).
  A `GROUP BY` column that the other grouping columns determine (functional
  dependencies from keys and equalities, `Rel.fds_sound`) moves into a `MIN`.
  A `GROUP BY` of left columns over a join on a key of the right side is
  computed before the join (eager aggregation).
  `sv.verify(...).optimized` is the rewritten plan.
* Key rules for ASOF (all in `Rel.keys_sound`): `ROW_NUMBER()` with the partition
  columns is a key (`windowRows_rowNumber_key`); a column `$i + c` of a non-NULL
  integer column can stand in for it in a key; a filter `$i = k` drops `i` from
  keys; join keys drop right-key columns the condition ties to the left side
  (`a.device = b.device`), for inner and left joins. A key of each branch of
  a `UNION ALL`, with a column whose values the branches cannot share (a
  constant tag, a `GROUPING` level), is a key of the union (`AVal.disjoint_ne`,
  #436).
* `window_tiebreak`, `Rel.window_deterministic` ([Keys.lean](../SubstraitLean/Keys.lean)):
  when a window's partition and sort columns contain a key of its input, every
  arrangement of the input sorted by the window's keys gives the same rows as
  `Rel.eval`. So the proofs describe what an engine computes, however it breaks ties.
* `orderFact_sound`, `winFacts_sound`, `WinFn.abs_sound`: what is known about
  `LAG`/`LEAD`/`ROW_NUMBER` columns holds. Strict order uses an oracle saying
  which windows have a key (`WindowKeys`); `Rel.keyedWindows_soundAll` proves the
  one computed from `Rel.keys` right, which is what `contract_sound` asks for.
* `IoT.window_complete` ([Completeness.lean](../SubstraitLean/Completeness.lean)): the
  converse of the contracts. If both sensors have valid readings at `t` and `t + 60`,
  the window at `t` is in the output, so no window is lost. It's built from one
  membership lemma per operator.

Doubles are modelled as exact integer codes (each double is a multiple of 2⁻¹⁰⁷⁴),
timestamps as microseconds; see [Float.lean](../SubstraitLean/Float.lean). The conversions
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

[Compose.lean](../SubstraitLean/Compose.lean) builds on `contract_sound`,
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

[Safety.lean](../SubstraitLean/Safety.lean) proves that a transformation runs without
runtime errors, or reports what may go wrong. `sverify` reports these as
`may fail: …` (a `VerificationError` from `@sv.transform`). A `SUM` that
may overflow is assumed to fit, `assumes: SUM of … fits 64 bits in every
group (checked at run time: the job raises if it does not …)` (or
`fits DECIMAL(38, 2)` for a decimal `SUM`, #316), and is an error with
`on_inferred="off"`.

* Errors, where the engines fail: integer division or remainder by zero, `MIN / -1`,
  integer `POWER` with a negative exponent or a result outside 64 bits,
  `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, a regular expression
  that may not compile, and `date_trunc` to a week, month, quarter or year outside
  ±2⁶³ nanoseconds (DataFusion panics or returns garbage there).
* `+`, `-`, `*` and negation leaving their declared width (64 bits, or narrower
  integers), and `date_trunc` to a day or less below `-2⁶³` µs, are errors too: the
  reference raises (#202), while DataFusion wraps around silently, which an error
  allows.
* An integer `SUM` leaving 64 bits, or a decimal `SUM` leaving its precision
  (`Measure.sumOk`, #316), is ruled out where the plan bounds a group's
  rows (`Rel.maxRows`: a `VALUES` list, a `FETCH` count) and the argument's range
  bounds each value (`Measure.sumFits`). Row caps on the inputs count too
  ([Rows.lean](../SubstraitLean/Rows.lean), #219): a capped read is a `FETCH`
  (`Rel.capReads`), and a join on a key of its right side is capped by its
  left side (`Rel.capJoins_eval`). Its `SUM`s are decided on the capped plan
  and every other issue on the plan as it is (`Rel.issuesCapped_sound`).
  Elsewhere it is an inferred assumption
  (`Rel.SumsFit`, `Rel.noIssue_of_sumsFit`) that the SQL checks on the data while
  the job runs.
* Bounds that rule out overflow are inferred
  ([Infer.lean](../SubstraitLean/Infer.lean), #244): the range analysis run
  backwards from each overflow `Rel.mayIssues` reports, through projections,
  filters, joins and `MIN`/`MAX` down to base-table columns. So are the
  ranges of codes that rule out domain errors, casts out of range, string
  lengths and decimal precision, and the value a divisor's column must not
  hold. The inference is
  untrusted and has no proofs. Its bounds are added to the preconditions and
  the contract is proved again (`contract_sound`, `Rel.mayIssues_sound`), so a
  wrong bound only makes that proof fail; on the data they are checked like
  any precondition.
* `Rel.mayIssues_sound`: every issue that can happen on any input is reported. Guards
  are understood where every engine respects them: in a `CASE` branch (and so
  `NULLIF(b, 0)`), or in a filter below a *projection*. They are not respected in the
  same `AND`, nor in an earlier *filter*: an engine may merge filters (`Rel.loose`;
  DataFusion does), so `t.filter(n != 0).filter(q % n > 1)` can fail.
* `FloatCode.floor_mono`, `round_mono`, `toInt?_mono`, `toInt?_of_range`
  ([Rounding.lean](../SubstraitLean/Rounding.lean)): `FLOOR`, `CEIL`, `ROUND` and the cast
  to `BIGINT` are exact on double codes and monotone, so `amount ∈ [0, 100]` proves
  `amount.round()` is an integer in `[0, 100]`, and the cast safe.
* Abstract rules for truncating `/` and `%` (`divBound_sound`, `modBound_sound`) and
  for squares (`powAbs_sound`).
* `Time.monthIndex_spec`, `Time.trunc_mono`, `Time.year_mono`
  ([Time.lean](../SubstraitLean/Time.lean)): every day lies in the month the calendar
  arithmetic computes, so years and truncations grow with the timestamp, and
  `ts ∈ [2024-01-01, 2025-01-01)` proves `ts.year() == 2024` and
  `ts.truncate("M") >= 2024-01-01`. The other parts have proved ranges (`day` in
  `[1, 31]`, …); `date_part` is `NULL` outside the years ±262142.

Trusted: *when* an engine evaluates an expression (`Rel.HasIssue`: `CASE` is lazy,
`AND`/`OR` are not, filter and join conditions may run before the filters below
them; [What is trusted](proofs.md#what-is-trusted)). `python/tests/test_numeric.py`
runs the plans on DuckDB and on the optional DataFusion on random data and checks
they only fail where an error was reported. `BIGINT` and timestamp columns are taken to
hold 64-bit values (from the schema); arithmetic on narrower integers is
checked at their declared width (#202, #419).

### Incremental view maintenance

Table updates are Z-sets: rows with signed weights, where a deletion has weight `-1` and an
update is a delete plus an insert. This follows DBSP (Budiu et al., VLDB 2023).
The linear fragment, `Rel.Incremental`, covers every operator except left,
semi and anti joins, `DISTINCT`, aggregates, fetch and windows; semi and anti
joins, `DISTINCT` and `COUNT`, `SUM`, `AVG`, `MIN` and `MAX` per group have
delta rules of their own ([section 6 of the optimizations note](optimizations.md#6-incremental-maintenance);
what refresh maintains is in [the guide](guide.md#nodes-composing-storing-refreshing)):

* `Rel.zeval_add`: `Q(D + ΔD) ~ Q(D) + ΔQ`. Filter, project, emit, sort and union
  are linear (a sort only orders the bag), and cross and inner join use the bilinear rule
  `Δ(A×B) = ΔA×(B+ΔB) + A×ΔB`.
* `Rel.delta`: compiles a plan into a delta plan, an ordinary `Rel` that reads the
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

[TableFormat.lean](../SubstraitLean/TableFormat.lean) covers what `sverify.io`
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
  `ChangeFeed.of_changed_files`: so is the diff of only the files that
  changed, if the unchanged files are the same rows in both snapshots.
* `stats_table`: with correct per-file statistics (`ColStats.Correct`,
  trusted), every row of the table lies in the join of the files' bounds;
  `stats_append`: the files an append added bound its rows; `stats_bounds`:
  that bound is the `IS NOT NULL AND c >= lo AND c <= hi` fact handed to the
  contract checker; `stats_fact`: with NULLs or a missing side it is
  `c IS NULL OR (…)`; `stats_all_null`: files that are all NULL give `c IS NULL`.
* `prune_sound`: filtering only the files that are not skipped gives the
  same rows as filtering the whole table, if no row of a skipped file makes
  the filter TRUE (which the checker proves from the file's statistics).

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and the trusted facts below. The bounds of `SUM` and `AVG` of doubles need none since D25: they are theorems about the correctly rounded sum (`floatSumCR_mem`, `floatAvgCR_mem`, `floatSumCR_sign`), and the bound of a sharded `SUM` too (`floatSplit_sum`); a sharded `AVG` divides natively and rests on `div_scaled_err` in `Float.lean`. The statistical aggregates need none since D30: they are the exact moments rounded once (`varOf_props`, `covOf_props`, `corrOf_props` are retired). The bounds of one double `+`, `-`, `*`, `/` and `exp` (#582) rest on five: `add_scaled`, `sub_scaled`, `mul_scaled`, `div_scaled` in `Float.lean` and `exp_fin` in `Safety.lean`; their signs (#441) on three: `add_nonneg`, `mul_nonneg`, `div_nonneg` in `Float.lean`. [`float-bounds/`](float-bounds.md) proves them for IEEE rounding with Mathlib, kept out of the core build (`div_scaled_err` is `core_div`'s statement).

## Modelling choices

How the Lean model represents and evaluates a plan (positional schemas,
bags as lists, the parser's rewrites, overflow, strings, elementary
functions and time) is in
[reference-semantics.md](reference-semantics.md#how-the-model-holds-a-plan).

## Prior work to build on

[prior-work.md](prior-work.md) credits the work sverify builds on, the formal
semantics of SQL in Coq and Lean among it, and compares sverify with related
tools.
