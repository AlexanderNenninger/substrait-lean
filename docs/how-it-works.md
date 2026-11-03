# How it works

How plans are checked, how the engines are made to agree, and exactly what
is proved. The user-facing side is in [guide.md](guide.md); the map of the
Lean files is in the [README](../README.md#the-lean-project).

```python
import ibis
import sverify as sv
from ibis import _
from sverify.engines import create_table

con = sv.connect()
create_table(con, "orders", ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
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
DuckDB (by default), Polars or DataFusion, using delta plans from Lean. A
node's `refresh` runs an incremental view (`sverify.incremental`, internal):

```python
import ibis
import sverify as sv
from sverify.engines import create_table
from sverify.incremental import IncrementalView

con = sv.connect()          # Arrow tables; plans run on DuckDB
orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
customers = ibis.table({"name": "string", "city": "string"}, name="customers")
create_table(con, "orders", orders.schema(), [(1, "ada", 30)])
create_table(con, "customers", customers.schema(), [("ada", "Paris")])
query = orders.join(customers, orders.customer == customers.name).select(orders.id, customers.city)
view = IncrementalView(con, query, "v")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 7)], deletes=[(1, "ada", 30)]),
            "customers": sv.Changes(inserts=[("bob", "Rome")])})
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
tables (`sverify.engines.create_table`, `con.arrow`), the engine plans run on, and Ibis
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
(`upstream/LEDGER.md` DD-4). Looking a scan up in `con.arrow` reads it into
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
means what [`docs/ibis-semantics.md`](ibis-semantics.md) says, with Ibis's
type promotions written as explicit casts. That makes plans typed: `qty >
amount` compares as doubles, where DataFusion's producer (from its unanalysed
plan) once left an integer next to a double's code (#16). Upstream's mistakes are fixed
(integer `/` divided integers, `where=` filters were dropped, sorts were always
`NULLS FIRST`, promotions could cast a double down to an integer, timestamp
literals were read in local time), and anything outside the model raises
`Unsupported`. `python/tests/test_ibis_substrait.py` checks every verified
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

Plans come from the Ibis producer or sverify's SQL lift, and they can run on
DuckDB (the default, below), [Polars](https://pola.rs) or DataFusion. You pick
one with `engine="polars"` on `node.refresh`, `sv.connect` or
`sverify.engines.run(con, plan, "polars")`. The tables stay in `con` and are handed to
the engine as Arrow. Engines are there for differential testing,
with the Lean semantics as the spec.

Polars runs Lean's own serialisation of the checked plan: the plan as
`substrait-check --write` writes it back out from the parsed `Rel`
(`sverify.engines.written_plan`), and the delta plans of `--delta`, which use the same
writer. `sverify/polars_engine.py` translates only that small, canonical form
to a `LazyFrame` and raises `Unsupported` on anything else. It does not go
through Ibis's Polars backend, which would compile a different plan. The
translator pins the semantics and takes no Polars defaults:

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
  `strpos` and `substring` count characters, and `substring` with
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
keys, three-valued filters, NULL and NaN order in windows, overflow, and each
runtime error and its guards. The
incremental-view tests run on both engines.

`python/tests/test_backends.py` runs every Ibis operation the coverage
harness verifies on random tables, on Polars and DuckDB against DuckDB running
Ibis's own SQL, and generates its Snowflake SQL and runs its Spark SQL on a local Spark session; `test_text.py` and `test_time.py` run their edge
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
view = IncrementalView(con, query, "v", engine="duckdb")

@sv.transform(ensures=[_.amount < 100], on_unproved="runtime", engine="duckdb")
def passthrough(orders): ...
```

The SQL generator (`python/src/sverify/sql/`) reads Substrait JSON as
`Parse.lean` does. It accepts exactly the plans `substrait-check` accepts and
raises `Unsupported` on everything else. It then writes SQL whose result is
`Rel.eval`. The query spells out every semantic choice and leaves none to
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
  by the ordinal), so the result has Lean's bits;
* strings: lengths and positions count characters, a negative `substring`
  start counts from the end unless the plan asks for `LEFT_OF_BEGINNING`
  (either way the start is normalized before it reaches the engine), and
  `LIKE` names its escape character;
* `date_part` and `date_trunc` use the engine's calendar functions where they
  agree with `SubstraitLean/Time.lean` (ISO weeks, `dow` from Sunday,
  milliseconds within the minute), and the SQL raises where DataFusion's
  calendar truncation fails;
* below a `FETCH`, a window or a sort, an ordinal column carries Lean's list
  order, so `LIMIT` and ties in sorts and windows pick Lean's rows, and a
  sorted result comes out in Lean's order.

Engine differences go through the hooks of a `Dialect`
(`sverify/sql/core/_base.py`). DuckDB's is `sverify/sql/duckdb.py`.

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

Snowflake support is aspirational: everything below has been checked on an
emulator; no real account was involved ([#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63)).

`to_sql(plan, SNOWFLAKE)` (from `sverify.sql.snowflake`) writes checked plans
and Lean delta plans as Snowflake SQL. The SQL is written to match Lean where
Snowflake's documented behaviour differs:

* integers are `NUMBER(38,0)` and are checked against the 64-bit range;
  division and remainder truncate (through `MOD`, as `/` rounds to six
  decimals), and `CAST(double AS BIGINT)` truncates and raises out of range;
* timestamps are `TIMESTAMP_NTZ(6)`; weeks, days of the week and truncation
  to a week use the ISO functions, independent of the session's `WEEK_START`;
* backslashes and control characters in strings are escaped;
* every identifier is quoted, so create tables and columns with quoted
  lower-case names.

Where Snowflake can't match, the plan is refused (`Unsupported`) or the query
raises when it would answer differently:

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
fakesnow emulates Snowflake on DuckDB, so this checks the SQL and says nothing
about Snowflake's behaviour. To run the same checks on a real account, set `SNOWFLAKE_ACCOUNT`,
`SNOWFLAKE_USER`, a credential (`SNOWFLAKE_PASSWORD`,
`SNOWFLAKE_AUTHENTICATOR` or `SNOWFLAKE_PRIVATE_KEY_FILE`) and
`SNOWFLAKE_WAREHOUSE`/`DATABASE`/`SCHEMA`.

#### Spark

`to_sql(plan, SPARK)` (from `sverify.sql.spark`) writes checked plans and
Lean delta plans as Spark SQL, for Spark 4 and Databricks SQL. With the
`spark` extra, `sverify.spark_engine.run(plan, tables)` runs a plan over Arrow
tables on a local session (or on the session you pass). The session needs the
settings of `SPARK_CONF`: ANSI mode
(`spark.sql.ansi.enabled`), without which an overflow wraps around and a bad
cast gives NULL, plus a pinned time zone, NTZ timestamps, case-sensitive
names and backslash escapes in string literals. The SQL matches Lean where
Spark differs:

* integers are `BIGINT`; division is `div` (`/` gives a double) and
  remainder `%`, both truncating; a `SUM` adds `DECIMAL(38,0)` values, since
  Spark raises when a partial sum overflows even if the total fits;
* doubles divided by zero raise, as the reference does (`on_division_by_zero`
  = ERROR); a plan asking for IEEE gets a `CASE` for ±inf or NaN;
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

Trusted components (not covered by the proofs): the JSON parser and
writer, the `sverify` glue (change tables, consolidation, merge), the Polars
translator, the SQL generator, and each engine's execution (DataFusion's
Substrait consumer, Polars, DuckDB's and Spark's SQL). These are covered by golden tests,
round trips and the differential tests instead.

The size hypothesis (trusted, stated in the theorems that use it): every
string has fewer than 2⁶² characters, and every relation a window reads fewer
than 2⁶² rows. No machine's memory holds more, and it is what bounds lengths,
positions and ranks: `Text.sizeCap` caps `CHARACTER_LENGTH`, `strpos`,
`levenshtein` and `ascii` there (a cap the hypothesis never reaches), and
`Rel.Small` is a hypothesis of `Rel.mayIssues_sound`, `Rel.guardFree_sound`
and `Rel.duckdb_sound`. So `ROW_NUMBER() - 1` and Ibis's `find` (`strpos - 1`)
are proved not to overflow without a precondition, while `amount * 2` still
needs one.

## How the results are checked

* Proofs: `lake build` re-checks every theorem. The main ones say that the
  update plan computes exactly the change to the result, and that running it on
  DataFusion with the weight-column encoding gives that result. See
  [Proven theorems](#proven-theorems).
* Randomized testing: `uv run pytest` generates random tables and random batches of
  inserts and deletes, including NULLs and duplicates. After every batch it
  checks that the maintained result equals a full recompute. This covers the parts
  the proofs don't: the JSON translation, the Python glue and the engine itself.

## What is proved

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
  the key, `DISTINCT` over it, co-partitioned joins and tie-free windows partitioned by it), and
  decomposable aggregates combine in two phases
  ([docs/optimizations.md](optimizations.md)).
* `Rel.evalI_eq`, `Rel.guardFree_sound`: a plan whose only possible issues are integer `SUM`s
  runs correctly without per-row checks.

### Contracts

[Contracts.lean](../SubstraitLean/Contracts.lean) is an abstract interpreter
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
  `least` get their bounds. `Expr.refine_sound` also covers `OR` and
  `IS NULL`, so a filter `x IN (1, 2, 3)` gives `x ∈ [1, 3]` and
  `x IS NULL OR x >= 0` gives "NULL or ≥ 0". `p OR q` is evaluated with `q`
  refined where `p` is not TRUE, also when `p` may be NULL (`orSplitNull`),
  which proves `x >= 0 OR x IS NULL` for a nullable `x`.
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
  (`a.device = b.device`), for inner and left joins.
* `window_tiebreak`, `Rel.window_deterministic` ([Keys.lean](../SubstraitLean/Keys.lean)):
  when a window's partition and sort columns contain a key of its input, every
  arrangement of the input sorted by the window's keys gives the same rows as
  `Rel.eval`. So the proofs describe what DataFusion computes, however it breaks ties.
* `orderFact_sound`, `winFacts_sound`, `WinFn.abs_sound`: what is known about
  `LAG`/`LEAD`/`ROW_NUMBER` columns holds. Strict order uses an oracle saying
  which windows have a key (`WindowKeys`); `Rel.keyedWindows_sound` proves the
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
`may fail: …` (a `VerificationError` from `@sv.transform`), or, for an
integer `SUM`, `may fail: SUM overflow: … (checked while the job runs …)`,
which does not block a proof.

* Errors, where DataFusion fails: integer division or remainder by zero, `MIN / -1`,
  integer `POWER` with a negative exponent or a result outside 64 bits,
  `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, a regular expression
  that may not compile, and `date_trunc` to a week, month, quarter or year outside
  ±2⁶³ nanoseconds (DataFusion panics or returns garbage there).
* `+`, `-`, `*` and negation leaving their declared width (64 bits, or narrower
  integers), and `date_trunc` to a day or less below `-2⁶³` µs, are errors too: the
  reference raises (#202), while DataFusion wraps around silently, which an error
  allows.
* An integer `SUM` leaving 64 bits is checked while the job runs (nothing bounds
  how many rows a group has): the SQL raises, and it does not make `proved` false.
* Bounds that rule out overflow are inferred
  ([Infer.lean](../SubstraitLean/Infer.lean), #244): the range analysis run
  backwards from each overflow `Rel.mayIssues` reports, through projections,
  filters, joins and `MIN`/`MAX` down to base-table columns. The inference is
  untrusted and has no proofs. Its bounds are added to the preconditions and
  the contract is proved again (`contract_sound`, `Rel.mayIssues_sound`), so a
  wrong bound only makes that proof fail; on the data they are checked like
  any precondition.
* `Rel.mayIssues_sound`: every issue that can happen on any input is reported. Guards
  are understood where DataFusion respects them: in a `CASE` branch (and so
  `NULLIF(b, 0)`), or in a filter below a *projection*. They are not respected in the
  same `AND`, nor in an earlier *filter*: DataFusion merges filters, so
  `t.filter(n != 0).filter(q % n > 1)` can fail.
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

Trusted: *when* DataFusion evaluates an expression (`Rel.HasIssue`: `CASE` is lazy,
`AND`/`OR` are not, filter and join conditions may run before the filters below
them). `python/tests/test_numeric.py` runs the plans on DataFusion and DuckDB on
random data and checks they only fail where an error was reported. `BIGINT` and timestamp columns are taken to
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

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Modelling choices

* Positional schemas. Substrait field references are ordinals, so a
  schema is just an arity. Types beyond "nullable value" are not tracked yet.
* Project appends, Emit narrows. This matches Substrait's `ProjectRel` +
  `RelCommon.emit`. Here `Emit` is its own node, and no rel carries an emit field.
* Bags as lists. `Rel.eval` returns a `List`, and plan equivalence is `List.Perm`.
  Several rewrites are stronger than that and hold as exact list equality.
* Windows sort stably. `Rel.eval` sorts a window's input with a stable merge
  sort, so ties keep input order. The checker only claims results for windows
  without ties (see `window_tiebreak`).
* Fetch is order-dependent. Without a `SortRel`, real engines may return any
  rows. The semantics fixes list order, so `fetch` theorems describe one valid behavior.
  `SortRel` is a stable sort here, while engines may order ties either way, so after
  `ORDER BY … LIMIT` the checker's claims hold for every row the engine could keep.
* Semi joins and `DISTINCT` are their own operators. `Rel.semi` keeps the left
  rows with some (or, for anti joins, no) matching right row; `Rel.distinct` keeps
  the first occurrence of every row (NULLs equal, doubles by their codes: one
  zero and one NaN). `DISTINCT` rows are a key (`Rel.keys`). DataFusion writes
  `DISTINCT` as an aggregate with one empty grouping, which its own consumer
  rejects; the parser reads it as "all columns".
* Aggregates have one grouping set. `Rel.aggregate` outputs one row per
  distinct grouping value (NULLs group together; doubles by their codes, so
  -0.0 and 0.0 are one group), or exactly one row without
  grouping expressions, even on an empty input. Measures skip NULLs; on no
  values `COUNT` is 0 and the rest are NULL. Integer `SUM` is exact (DataFusion
  wraps around; the reference raises outside 64 bits, checked while the job runs), double `SUM`/`AVG` add with native floats
  (DataFusion promises no order), and `AVG` of integers is the `AVG` of their
  conversion to double. `MIN`/`MAX` of doubles compare by the
  codes, as DuckDB does; DataFusion's grouped version turns a group of +∞ into
  the largest finite double and skips NaN next to other values, so it is refused
  there. Contracts see `MIN`, `MAX`, an integer `AVG` and a decimal `AVG` within
  the values' bounds, measures over a group of a column that is never NULL as
  never NULL, and `MIN ≤ MAX` (#372). An `AVG` of doubles rounds, so it is some
  double.
  The grouping columns are a key of the result.
* Ill-typed calls evaluate to `null`. This keeps `eval` total. `Rel.WF` rules out
  out-of-range field references.
* Some operations are rewrites in the parser. `IN` lists become `OR`s of
  equalities; `COALESCE`, `NULLIF`, `GREATEST`, `LEAST` and `ABS` become
  conditionals; `RIGHT JOIN` becomes a `LEFT JOIN` with its sides swapped;
  `FULL OUTER JOIN` becomes the left join plus the anti join of the right side,
  padded with NULLs; `x IN (subquery)` in a filter becomes a semi join on `=`;
  `UNION` is `DISTINCT` of `UNION ALL`; `IS NOT DISTINCT FROM` becomes a
  conditional. The rewrites are trusted code, checked against DuckDB by
  `python/tests/test_rewrites.py` and `python/tests/test_relations.py`. (`ABS` of the smallest `BIGINT` fails in
  DataFusion; here it is reported as an overflow.)
* Overflow is an error at the declared width. `Rel.eval` computes exact
  integers, and [Safety.lean](../SubstraitLean/Safety.lean) reports every operation whose
  result may not fit its declared width (64 bits, or narrower integers). Where DataFusion fails instead (division, `POWER`, casts), the
  value in the model is `NULL`.
* Strings are Unicode scalar values. `substring`, `strpos`, `LIKE`, `btrim`, `||`,
  `character_length`, `repeat`, `reverse`, `replace`, `ascii` and `levenshtein` are
  computed exactly, checked against DuckDB (and Rust's string functions, as
  DataFusion computes them) by `python/tests/test_text.py`; a
  `repeat` of more than 2³¹ - 1 bytes is an error, as in DataFusion. `UPPER`, `LOWER`,
  `ILIKE`, regular expressions, `md5` and `sha256` are black boxes (`opaque`): no proof
  depends on what they compute. Lean's evaluator handles only ASCII case, and evaluates
  regular expressions with RE2's leftmost-first matching ([Regex.lean](../SubstraitLean/Regex.lean))
  where RE2 and Rust agree, checked against DuckDB by `python/tests/test_regex.py`.
  `translate` is refused: DataFusion translates grapheme clusters. A pattern is an error
  (for `regexp_match`) or refused (for `regexp_extract` and `regexp_replace`) unless
  `Text.simpleRegex` accepts it, a conservative subset of Rust's and RE2's syntax that is
  tested to compile in both.
* Elementary functions follow Substrait, with errors outside their domains.
  `sqrt`, `exp`, `ln`, `log10`, `log2`, `logb`, the trigonometric functions and
  `atan2` are computed with C's libm ([Numeric.lean](../SubstraitLean/Numeric.lean)), and
  contracts treat each result as "some double". Outside a function's domain (`sqrt` of a
  negative, the logarithm of zero or a negative, `asin` and `acos` outside `[-1, 1]`,
  `atan2(0, 0)`, `logb` to a base that is not positive or is 1) the result is an error,
  Substrait's `on_domain_error` = ERROR when a plan omits the option; NaN is in every
  domain. Bitwise operations are exact in 64-bit two's complement, and a shift count
  outside 0–63, which Substrait leaves open, is an error too. Polars and the SQL of
  DuckDB raise where Lean reports a domain error; DataFusion returns NaN, ±∞ or a
  wrapped shift there, which an error allows. Spark runs `sqrt` and the bitwise
  operations (its other functions are Java's `StrictMath`); Snowflake runs `&`, `|` and
  `^` only (its shifts are not 64-bit, and its libm is not documented). Checked by
  `python/tests/test_math.py`.
* Timestamps are microseconds (UTC). `date_part` and `date_trunc` are computed
  exactly, checked against DuckDB and DataFusion by `python/tests/test_time.py`, including at
  the ends of the ranges where DataFusion stops being exact. Dates (`DATE`) are not
  supported by them yet.
* Integer `//` from Ibis is exact. Ibis compiles it through doubles
  (`CAST(FLOOR(CAST(a AS DOUBLE) / b) AS BIGINT)`), which is wrong beyond 2⁵³;
  `sverify` compiles it to integer division instead.

## Prior work to build on

We found no formal semantics for Substrait. The closest work formalizes SQL or relational algebra:

Coq (most mature)
* SQLCert / SQL_Coq (Benzaken, Contejean): a mechanized semantics for
  realistic SQL with nulls, aggregates and correlated subqueries, an extended bag
  algebra, and proofs of common optimizer rewrites.
  [HAL 01487062](https://hal.archives-ouvertes.fr/hal-01487062),
  [HAL 01955433](https://hal.archives-ouvertes.fr/hal-01955433)
* HoTTSQL (Chu, Weitz, Cheung, Suciu; PLDI 2017): denotes queries as
  K-relations using univalence. It proves many rewrite rules, and the Cosette prover grew out of it.
  [arXiv 1607.04822](https://arxiv.org/abs/1607.04822),
  [PLDI page](https://pldi17.sigplan.org/event/pldi-2017-papers-hottsql-proving-query-rewrites-with-univalent-sql-semantics)
* A Formalization of SQL with Nulls (Ricciotti, Cheney; JAR 2022): covers
  three-valued logic, set and bag operations, lateral joins and nested subqueries.
  [arXiv 2003.11331](https://arxiv.org/abs/2003.11331),
  [PMC9637088](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC9637088/)
* Q\*cert (Auerbach et al., SIGMOD 2017): a verified query compiler
  built around the nested relational algebra (NRA<sup>e</sup>). It's the closest
  analogue to "verified IR for queries".

Lean 4
* RelationalAlgebra (Rickerd): relational algebra ≡ first-order logic, built on Mathlib.
  [Reservoir](https://reservoir.lean-lang.org/@Rickerd1234/RelationalAlgebra)
* provenance (Senellart): semantics for ProvSQL with semiring provenance,
  a natural route to K-relation semantics in Lean.
  [Reservoir](https://reservoir.lean-lang.org/@PierreSenellart/provenance)
* Emergence AI's [Lean SQL equivalence write-up](https://www.emergence.ai/blog/formal-verification-of-sql-queries-in-lean-for-enhanced-accuracy)
  and the typed-queries chapter of
  [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Worked-Example___-Typed-Queries/).
