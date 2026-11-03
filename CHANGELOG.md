# Changelog

## 0.4.0 (2026-11-03)

### Breaking changes

Upgrading from 0.3.0, check these first. Each has its own entry below.

- `sv.sql(query)` uses the reference semantics by default, as `sv.verify` and
  `@sv.transform` do (#411). Write `sv.sql(query, semantics="duckdb")` where
  you relied on DuckDB's NaN and `±inf`.
- SQL strings are DuckDB's SQL, read by sverify's own lift. DataFusion's SQL
  planner (#211) and Isthmus (#253) are gone as frontends:
  `sverify.engines.isthmus_json`, `sverify.engines.SQL_PRODUCERS`,
  `sv.connect(sql_producer=...)`, `SVERIFY_ISTHMUS` and `sverify.engine.to_sql`
  are removed. In DuckDB's SQL `7 / 2` is 3.5; write `7 // 2` for integer
  division. `sverify.engines.to_sql` writes SQL from a checked plan.
- `@sv.transform(strict=True)` is `@sv.transform(infer=False)`, and
  `ContractedTransform.strict` is `.infer`, with the opposite truth value
  (#409). `strict=` still works and warns.
- `sv.references(col, table, other)` is
  `sv.references(col, to=other_table.other)` (#412). The positional form still
  works and warns.
- `Connection.datafusion` is deprecated and warns (#413). Run DataFusion
  through `engine="datafusion"`.
- Integer overflow at the declared width is an error that makes a report
  unproved, where it was a warning (#202). Inferred bounds (#244) discharge
  most of it; for the rest, the report's hint names the bound to add to
  `requires`. An integer `SUM` that may overflow is listed in
  `Report.assumed` and checked on the data.
- A double divided by zero raises (#204), and no operation creates a NaN
  (#257): `verify` reports both unless the plan rules them out. Bound the
  divisor or the operands in `requires`, or filter.
- Strings have fewer than 2³² characters, and `substring` with an offset or
  length outside that range is an error (#336). `verify` reports it for a
  column offset unless `requires` bounds it, for example
  `_.start >= -2**32` and `_.start < 2**32`.
- Arithmetic on `FLOAT` (fp32) is refused (#208); cast to `DOUBLE` first.
- No wheels for Intel macOS. There pip and uv build sverify from the sdist,
  which needs [elan](https://github.com/leanprover/elan).
- The maintainer tooling (`sverify.coverage`, `sverify.catalogue`,
  `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`, `sverify.examples`)
  is no longer in the wheel.

### DuckDB writes Delta and Iceberg sinks

When a node runs on DuckDB, its `DeltaSink` and `IcebergSink` have DuckDB
write the Parquet files, and sverify commits them with the contract and the
epoch, exactly once as before. The state and the rows never pass through
Python. A Delta change rewrites only the files that hold deleted rows and
adds a file of the new rows, in one commit with delta-rs's statistics; an
Iceberg change is a data file with field ids and a position delete file.
Other engines, partitioned or remote tables, and an overwrite by another
plan write through delta-rs and pyiceberg as before.

A Delta sink no longer mistakes its own constraint for a foreign one when the
node's guarantee has a decimal number: Delta stores `x >= 0.0` as `x >= 0`
(#173).

### Incremental views keep their state in DuckDB

On DuckDB, an incremental view's state no longer lives in Python: DuckDB
holds it between refreshes, and the view's rows are a DuckDB view of it. On
every engine, states and changes are added up by one plan Lean checks (a
union, grouped by every column, with the weights summed), so they group rows
as the model compares them: one NaN, `-0.0` equal to `0.0`, lists by their
elements. Sinks compute their change with the same plan (#173).

A view's rows, and what a sink writes, come in no particular order, as a
SQL query's do; before, they kept the order in which rows first appeared.

### Refreshes on DuckDB cost what changed

On DuckDB, a refresh no longer rebuilds a view's whole state. The merge plan
adds the change to the state rows it touches, and DuckDB replaces those rows
in place, in one transaction for every view: a refresh that changes ten rows
of a view of ten million costs about ten rows. Sinks write the sum of the
view's changes since the state they wrote. A view whose new contents a
recomputed view or `refresh(audit=True)` reads first is still merged in full
(#173).

### Delta and Iceberg tables read natively by DuckDB

On DuckDB, a `DeltaSource` or `IcebergSource` is no longer loaded into
Python. The pipeline holds the Parquet files of the table's version, chosen
by sverify's own pruning (#81, #108), with the rows that deletion vectors or
position delete files remove, and DuckDB reads them with `read_parquet`.
Refreshes keep the table as the files of the new version. Partitioned tables,
Delta column mapping, renamed Iceberg columns, equality deletes, object
stores and the other engines read through Arrow as before.
`scripts/bench_io.py` measures reading, refreshing and writing at scale (#173).

### The reference is a relation: an engine returns an allowed result or raises

`docs/reference-semantics.md` now defines correctness through the set of
results the reference allows for each input (`Rel.Allowed`,
`SubstraitLean/Allowed.lean`). The set holds more than one result where the
reference leaves a choice to the engine: the order of rows and of ties,
`FIRST`/`LAST` and `distinct(on=)` without an order, the order in which a double
`SUM` or `AVG` adds (#85), and the statistical aggregates. `Rel.eval` is one
allowed result (`Rel.eval_allowed`); a plan without choices allows only its
rows (`Rel.allowed_perm_eval`); rewrites are refinements (`Rel.Refines`); and
the DuckDB shim and guard elimination return allowed results. The page also
lists where the reference overrides Substrait (one zero, one NaN, the size
hypothesis), states principle 3 as "Every engine can follow it with reasonable
effort", and notes that `fp32` arithmetic is refused until #417.

### Integer overflow is an error at the declared width

Breaking: `+`, `-`, `*` and negation of integers whose result does not fit
its declared type (`BIGINT`, or `INTEGER`, `SMALLINT`, `TINYINT`) raise, on
every engine, where a plan omits `overflow` or asks for `ERROR` (#202). An
overflow `verify` cannot rule out makes the report unproved; it was a "may
wrap around" warning. Inferred bounds (#244) discharge most of these, and the
report's hint names the bound to add to `requires` for the rest. The
arithmetic sverify adds itself (0-based `row_number`, `find`, floor
division) is proved free of overflow, under the hypothesis that a window
reads fewer than 2⁶² rows (#254).

### An integer `SUM` that may overflow is an assumption checked on the data

`verify` no longer treats a possible integer `SUM` overflow as a warning. Where
the plan bounds a group's rows (a `VALUES` list, a `FETCH` count, an aggregate
without groups) and `requires` bounds the column, the overflow is ruled out.
Elsewhere sverify assumes each sum fits 64 bits, as it assumes inferred bounds
(#244), and lists it in `Report.assumed`; the SQL it writes checks it on the
data while the job runs. With `infer=False` it is an error that makes the
report unproved. A row cap (`sv.max_rows`, #219) discharges it statically. A
window `SUM` or `AVG` whose frame may hold both `+inf` and `-inf` is now
reported as a domain error, as the grouped one is (#257).

### A double divided by zero raises

`x / y` and `x % y` on doubles raise on a zero divisor, as on integers, when
the plan omits `on_division_by_zero` or asks for `ERROR` (#204). `verify`
reports "division by zero" unless the plan rules it out (`y > 0` in
`requires`, a filter, `NULLIF(y, 0)` or `CASE WHEN y <> 0`). A plan that asks
for `IEEE`, `LIMIT` or `NULL` gets that. Under `semantics="duckdb"`, SQL
divides as DuckDB does, giving `±inf` or NaN.

### Fixed: aggregates of double constants, casts between dates and timestamps

The reference computed two kinds of plans wrongly (#201). An aggregate of a
double constant read the constant as an integer: `SUM(CAST('inf' AS
DOUBLE))` is now `inf`, and `avg(42) OVER ()` is `42.0` (#205). A cast
between a date and a timestamp kept the number of days or microseconds: a
date now becomes midnight of that day, and a timestamp rounds down to its
day, before 1970 too. A comparison of a date with a timestamp without a cast
is refused (#206).

### Lists compare element by element

`<`, `>`, `ORDER BY`, `MIN` and `MAX` on lists order them lexicographically,
a proper prefix first (#207). A NULL element that decides a comparison makes
it NULL (`[1, NULL] < [1, 3]`); in `ORDER BY`, `MIN` and `MAX` NULL elements
sort after every other value
([reference semantics](../docs/reference-semantics.md)).

### Arithmetic on `FLOAT` (fp32) is refused

The reference computed `FLOAT` arithmetic in doubles, so `2e38::FLOAT / 0.1`
gave `2e39` where every engine gives `inf`. Arithmetic on `FLOAT`s and casts
to `FLOAT` are refused until binary32 is modelled (#208, #417). Reading a
`FLOAT` column, comparing it and widening it to `DOUBLE` are exact and keep
working; cast to `DOUBLE` first to compute with it.

### `avg` of integers follows the plan's output type

An `avg` of integers whose plan declares an integer result, as Substrait's
`avg` of `i64` does, is the exact mean truncated toward zero; a declared
`fp64` result is the mean as a double (#209). Other output types are refused.

### `substring` counts a negative start from the end

A plan that omits `negative_start` counts a negative start from the end of
the string, as DuckDB does: `substring('hello', -2, 2)` is `'lo'` (#209).
A plan that asks for `LEFT_OF_BEGINNING` gets that, and `ERROR` is refused.
The SQL writers and Polars rewrite the start before calling the engine's
`substring`.

### SQL strings are DuckDB's SQL, through sverify's own lift

`sv.sql`, `sv.verify` of a SQL string, SQL conditions in contracts, Ibis's
`Table.sql` and `Backend.sql`, and `sverify.engines.substrait_json` now read
**DuckDB's SQL** and plan it with sverify's own SQLGlot lift
(`sverify.sql_lift`, #239). DataFusion's SQL planner is gone as a frontend
(#211); DataFusion stays an execution backend (`engine="datafusion"`), and SQL
strings no longer need the `datafusion` extra.

This changes what some SQL means. In DuckDB's SQL, `/` divides as doubles
(`7 / 2` is 3.5; integer division is `//`), `1.5` is a `DECIMAL(2, 1)` rather
than a double, and NULLs sort last in both directions. A double divided by
zero raises under the reference semantics, the default (#411), and is `±inf`
or NaN with `semantics="duckdb"`. The entries for #240 list what the lift
reads; anything else is refused, saying what. Write those queries in Ibis
meanwhile.

### Row caps prove integer SUMs fit

A row cap `sv.max_rows(n)` in `requires` now proves integer `SUM`s fit 64
bits (#219): a `SUM` of values in `[-m, m]` over at most `n` rows, with
`n · m < 2⁶³`, is no longer an assumption checked on the data
(`Report.assumed`). Lean carries the caps through filters, unions, limits,
aggregates and joins. A join on a `unique` key of its right side keeps the
left side's rows (`Rel.capJoins_eval`), where a product would be far too
large. Caps are now:
- proved from the record counts of a Delta or Iceberg table's files;
- checked on every batch of an incremental view;
- proved in `ensures`.

`Report.rows` bounds the output's rows, and the SUM hint names the cap that
proves a sum fits.

### Casts between doubles, decimals and integers keep their bounds

- `CAST(x AS DECIMAL(p, s))` of a double whose bounds are known no longer
  reports a failed cast or a precision overflow when the casts of the bounds
  fit: after `WHERE f BETWEEN 0 AND 100`, `CAST(f AS DECIMAL(10, 2))` is safe
  (#223).
- `CAST(d AS DOUBLE)` of a decimal keeps the decimal's bounds, as
  `CAST(n AS DOUBLE)` of an integer already does. TPC-H Q08's contract is now
  proved, and Q14's division can no longer be by zero.
- The reference computes these conversions exactly (the nearest double,
  halves to even; `round(x · 10ˢ)` in doubles for the cast to a decimal) and
  states what they keep: monotone, within `2⁻⁵³` relatively, exact for
  integers up to `2⁵³`, which survive the round trip to a double and back.

### Benchmark catalogue refreshed for 0.4.0

The catalogue's 54 benchmark queries were probed again on 0.4.0. 53 are accepted and 53 now have a contract, of which 46 are proved and 49 run as verified SQL on DuckDB (#229). New contracts: TPC-DS q27 and q36 (ROLLUP lifts since #306) and H2O groupby q9 (`corr`). A query written in SQL now states its contract as SQL conditions.

TPC-H q11, q14 and q20 state row caps from the specification's largest scale factor. Each query still short of proved or verified SQL says why in its TOML, with the issue that would close it: SUMs bounded by row caps (#470), RANK over a ROLLUP (#471), keys through a FULL JOIN (#472) and ROW_NUMBER filters projected past their ties (#473).

### The SQL written for DuckDB is proved to return the reference's rows or raise

`Rel.duckdb_shim_sound` (`SubstraitLean/Profile.lean`) proves that DuckDB,
running the SQL sverify writes, returns `Rel.eval`'s rows or raises, for any
plan, with no contract needed (#185). Engine profiles state what DuckDB
computes for each function, and where it differs from the reference the
written SQL compensates ([engine profiles](../docs/engine-profiles.md)). The
query catalogue records, for each benchmark query, whether it is verified SQL
on DuckDB (`verified_sql` in [`catalogue/INDEX.md`](../catalogue/INDEX.md),
#229).

### Plans with `NOT IN` subqueries and decimals are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. A `NOT IN (subquery)`, or a `CASE` of several
branches, grew on every reading, so such a plan stopped at "this decimal
arithmetic cannot be written for the engines yet" (#238, TPC-H Q16's
shape). It is written now.

### `AVG` of a DECIMAL as a double

DuckDB SQL that averages a DECIMAL column, such as TPC-H Q1's
`avg(l_quantity)`, is now verified. DuckDB returns a DOUBLE, and so does
the plan: the exact sum, converted to a double, divided by the count. NULL
without values. Over windows it is still refused.

### Plans with decimals and a negated double are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. Negating a double, or taking its `ABS`, broke that,
so such plans (TPC-DS q89, for one) stopped at "this decimal arithmetic
cannot be written for the engines yet". They are written now.

### The SQL lift reads dates and timestamps

The SQL lift now reads dates and timestamps (#240): `EXTRACT`, `date_part`,
`year()` and its kin, `DATE - DATE`, `datediff('day', …)`, `date_trunc` of
a date, and a date or timestamp plus or minus a constant interval. Adding
months clamps to the month's last day, as in DuckDB. DuckDB types
`DATE ± INTERVAL` and `date_trunc` of a date as TIMESTAMPs. They compare
exactly with dates, but as an output column or next to a timestamp column
they need a cast of a date column to a timestamp the model lacks yet, and
are refused.

### The SQL lift reads GROUPING SETS, ROLLUP and CUBE

The SQL lift now reads `GROUP BY` with `GROUPING SETS`, `ROLLUP` and `CUBE`, alone or next to plain keys, and `GROUPING(…)` in the select list, HAVING, ORDER BY and window functions (#240). Each grouping set becomes its own aggregate, with NULL for the keys the set leaves out and the value of each `GROUPING(…)` as a constant. The aggregates are joined with `UNION ALL`, as DuckDB computes them. On empty input, the empty set's grand-total row is kept.

Two fixes came with it:
- A window function's `PARTITION BY` and `ORDER BY` may now be expressions, not only columns. The plan computes them as columns first, since the model reads them as columns.
- In an `ORDER BY` expression, a bare name is the output column of that name, as in DuckDB. For example, `ORDER BY CASE WHEN s > 0 THEN customer END` where `s` is an alias.

TPC-DS q27 and q36 now pass: 51 of 54 benchmark queries agree.

### The SQL lift refuses joins it would have read wrongly

The sqllogictest replay found queries the SQL lift read wrongly (#240). It now refuses them instead:
- **`ASOF JOIN` and `POSITIONAL JOIN`:** the lift read these as the inner join of their `ON`, or as a cross join. An ASOF join keeps each left row's latest match; a POSITIONAL join pairs rows by position.
- **`t.*` with `JOIN … USING`:** SQLGlot leaves the `USING` columns out of the right table's `t.*`, where DuckDB keeps them. `SELECT *` and listed columns still work.
- **Ordering comparisons (`<`, `<=`, `>`, `>=`) of structs:** DuckDB orders them field by field, with NULLs last, and the model's order differs. Lists still compare as DuckDB's, and equality still works.

Other queries the replay found read wrongly are refused or fixed too:
- **Clauses SQLGlot attaches to a table:** `TABLESAMPLE`, `PIVOT`, and the comma joins of a FROM-first query (`FROM a, b SELECT …`) are now refused. The lift used to read only the table and drop them.
- **Numbers with an underscore not between two digits** (`1__2`, `1._5`): DuckDB reads such an underscore as the start of an alias, SQLGlot as a digit separator (upstream/LEDGER.md SG-4). These are refused.
- **A constant that doesn't fit its cast's type** (`200::TINYINT`, `12.5::DECIMAL(2,1)`): the lift now writes the cast instead of an out-of-range literal. A string read as a decimal is read exactly, so `'1e38'::DECIMAL(38,0)` no longer goes through a double.
- **INTERVAL output columns:** these are refused, because the model holds intervals as microseconds while DuckDB keeps months and days apart.
- **Casts to the `NULL` type:** refused.

### The SQL lift reads numeric functions, DISTINCT and FILTER in aggregates

The SQL lift now reads (#240):
- **Numbers:** `power` (`**`, `pow`), `abs`, `round`, `floor`, `ceil`, `sign`, `isnan`, `greatest`, `least`, `nullif`, and `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`.
- **Comparisons:** `IS [NOT] DISTINCT FROM`.
- **Aggregates:** `DISTINCT` in every aggregate, and `FILTER (WHERE …)`.

They have DuckDB's meanings:
- `power` and the elementary functions compute in doubles;
- `log(x)` is base 10;
- `greatest` and `least` leave NULLs out;
- `sign` is a TINYINT, 0 for NaN;
- `isnan(NULL)` is NULL.

Outside their domain (`sqrt(-1)`, `ln(0)`), DuckDB gives NaN or `-inf`. The plan states that preference and then `ERROR`, the reference's, which the model takes, so `verify` reports such rows as possible errors.

### The SQL lift reads strings

The SQL lift now reads strings (#240): `length`, `substring`/`substr` (from
1; a negative start counts from the end), `trim`/`ltrim`/`rtrim` (spaces,
or the characters given), `strpos`/`instr`/`position`, `contains`,
`starts_with`, `ends_with`, `prefix`, `suffix`, `LIKE`/`ILIKE` and their
`NOT`, `||`, `concat` (which leaves NULLs out), `replace`, `repeat`, `left`,
`upper` and `lower`. A LIKE pattern must be a constant without a backslash:
DuckDB's LIKE has no escape character, and the model's has one. `reverse`
is refused, because DuckDB reverses grapheme clusters.

### The SQL lift reads CTEs, subqueries and more joins

The SQL lift now reads (#240):
- **CTEs:** non-recursive `WITH`, inlined where each is read; a later CTE may read an earlier one.
- **Uncorrelated subqueries:** a scalar subquery (the checker must prove it has at most one row: an aggregate without groups, or `LIMIT 1`), `x [NOT] IN (SELECT …)` with SQL's rules for NULLs, and `EXISTS (…)`.
- **More joins:** `SEMI`, `ANTI`, `RIGHT` and `FULL` joins.

A subquery that reads a column of the query around it (a correlated subquery) is refused, saying so; write it as a join, or as a `SEMI` or `ANTI` join.

### The SQL lift reads window functions

The SQL lift now reads window functions (#240):
- **Ranking:** `row_number`, `rank`, `dense_rank`, `percent_rank`, `cume_dist` and `ntile`.
- **Values:** `lag` and `lead` (a constant offset, and a default), `first_value`, `last_value` and `nth_value`.
- **Aggregates:** `sum`, `avg`, `count`, `min` and `max` over a window, including windows over a query's aggregates (`rank() OVER (ORDER BY sum(x))`).
- **Frames:** `ROWS` and `RANGE` frames with integer offsets, and DuckDB's default frame: to the current row and its peers with an `ORDER BY`, the whole partition without.

`ntile` is DuckDB's, the SQL standard's buckets: 6 rows in 4 tiles are 1 1 2 2 3 4. The lift writes it from `row_number` and `count`, because the model's own `ntile` is DataFusion's. Named windows (`WINDOW w AS …`), `GROUPS` frames, `EXCLUDE`, `IGNORE NULLS` and `DISTINCT` in a window are refused.

### `NTILE` deals out buckets as SQL does

`NTILE(k)` now follows the SQL standard, as DuckDB, Spark and Snowflake
compute it: the first `n % k` buckets hold one row more. It used to follow
DataFusion's formula, which spreads the larger buckets out (`ntile(4)` of
10 rows gave `1 1 1 2 2 3 3 3 4 4`; now `1 1 1 2 2 2 3 3 4 4`). DataFusion
is refused for `NTILE` for now. `verify` still proves `1 ≤ NTILE ≤` the
row's number.

### The DuckDB replay's ledgers come from the SQL lift

`characterization/duckdb/*.json` now record the sqllogictest replay through the SQL lift on `main`, with #338's fixes (#240). Over 121 areas and 46,283 queries: 8,449 agree, 265 disagree, 22,931 refused, 14,638 skipped. The README's summary table is regenerated.

The replay itself:
- logs queries slower than 10 s;
- writes its summary table again: it no longer fails on `probes.json`.

Two lift regressions from #338 are fixed:
- A string read as a decimal rounds half away from zero past the scale, as DuckDB does, instead of being refused.
- A double constant is folded into a decimal where the decimal holds it exactly (`1e1::DECIMAL(38,0)`).

### `AVG` of a DECIMAL over a window as a double

`avg(d) OVER (...)` of a DECIMAL column in DuckDB SQL is now verified, as a
DOUBLE the way DuckDB types it, and arithmetic with it is in doubles (as in
TPC-DS q89's `sum_sales - avg_monthly_sales`).

### DuckDB's SQL writes the proved lowering

Where DuckDB computes a function differently from the reference, the SQL
sverify writes for DuckDB is now the template the Lean build generated and
proved (`substrait-check --lowering-table`, read by `sverify.sql.lowering`):
the guards for NaN and ±inf, the elementary functions' domains, division and
`%` by zero, `MIN % -1`, `<<`, and `overflow` = `SILENT` or `SATURATE`. The
hand-written versions in `sverify.sql.duckdb` are gone. Polars no longer
raises on a shift of NULL by an out-of-range amount, which the reference
leaves NULL (#241).

### Integer overflow can wrap around or clamp when a plan asks

A plan may now set `overflow` to `SILENT` (wrap around) or `SATURATE` (clamp)
on integer `add`, `subtract`, `multiply` and `negate`, at the declared width
(`i8` to `i64`); before, these were refused (#255). Nothing raises for them,
so `verify` reports no overflow. DuckDB runs them in 128-bit arithmetic, with
templates the Lean lowering generator found and proved (`SATURATE`) or a
hand-written, proved schema (`SILENT`); the other engines refuse them for now
([#241](https://github.com/AlexanderNenninger/substrait-lean/issues/241)).

### DuckDB's functions probed for the options they implement

`substrait-check --outcomes` evaluates each row of a projection over `VALUES`
under the reference and prints the value or the error raised. The maintainer
tool `python -m sverify_dev.probe` uses it to run DuckDB's arithmetic and
elementary functions on edge cases under every combination of
`error_on_division_by_zero` and `ieee_floating_point_ops`, and to keep the
Substrait options whose outcomes match
(`characterization/duckdb/probes.json`, FACTS R15). It corrected two facts:
double division by zero is IEEE under DuckDB's defaults, and `MIN % -1`
raises (#242).

### DuckDB's profile says what DuckDB computes, and the lowering compensates

`Profile.duckdb` now states DuckDB 2.0's behaviour where the probes found it
differs from the reference: NaN for operations on doubles that have no value
(`∞ - ∞`, `0 · ∞`, `∞ / ∞`, `sqrt(-1)`), `-∞` for a logarithm of 0, IEEE
division by zero for doubles (`ieee_floating_point_ops`, a new setting),
`atan2(0, 0) = 0`, `MIN % -1` raising, and the shifts. The generated lowering
to DuckDB guards each of them, every guard proved by the kernel, and
`Rel.duckdb_sound` is restated for DuckDB's IEEE mode, with the SQL printer
trusted for `MIN % -1` and `<<`, which it writes out. The lowering generator
keeps its results in `SubstraitLean/LoweringCache.lean`
(`substrait-check --lowering-cache`), so builds try each known template first
(#242).

### Engine facts as JSON documents, with provenance

What DuckDB does, judged against the reference semantics, is now one JSON
document per finding in `characterization/duckdb/facts/`, in the format of
`characterization/fact.schema.json`: the engine version checked, what the
engine and the reference do, a status, and each check's date, method, tool
and evidence (DuckDB's tests at their commit, the replay ledgers, the probe
verdicts of `probes.json`). DataFusion 51's findings from the replay are in
`characterization/datafusion/facts/`. `characterization/<engine>/FACTS.md`
is generated from them by `python -m sverify_dev.facts --write`.

### Inferred bounds against overflow

Contracts no longer have to state the bounds that rule out integer overflow
(#244). For `amount * 2` on a `BIGINT`, sverify infers `_.amount < 2**62`,
proves the contract with it, and treats it as a precondition: it is checked
on the data at call time and on every refresh, or proved from Delta and
Iceberg file statistics, and reports list it as inferred. The inference
covers `+`, `-` and `*` with constants or bounded columns, negation, `abs`,
narrow integers and timestamp truncation (#379), through projections,
filters, joins and `MIN`/`MAX`. Lean proves the contract again with the
inferred bounds, so a wrong inference only fails the proof. Where no single
bound exists (the product of two columns, a `SUM`, a value from another
contracted transformation), the report's `Issue.hint` suggests one.
`@sv.transform(infer=False)` and `sv.verify(..., infer=False)` require
explicit bounds.

### Inferred preconditions for more runtime errors

Sverify now infers preconditions for runtime errors besides integer
overflow, as #244 does for overflow. Each is the weakest per-column
condition, marked "(inferred)", checked on the data or proved from metadata,
and switched off by `infer=False`:
- division and remainder by zero: `(_.b != 0)`;
- domain errors: `sqrt`, logarithms, `asin`/`acos`, a fractional power;
- casts out of range: to narrower integers, and from doubles to `BIGINT`;
- `repeat` counts;
- decimal precision of `+`, `-` and `*`;
- date arithmetic.

Where no single bound exists (`∞ / ∞`, `substring` offsets counted from
either end, the sum of two unbounded decimals), the hint suggests one and
nothing is assumed ([docs/guide.md](docs/guide.md#inferred-bounds)).

### Suggested preconditions for unproved postconditions

An unproved postcondition that compares a value with a constant now comes
with the precondition on the inputs under which it holds: `_.doubled <= 100`
with `doubled = qty * 2` reports "would hold with `(_.qty < 51)` in the
requires of 'items'". Sverify proves each suggestion before showing it and
never assumes one. `CheckedCondition.suggested` and `Report.suggestions`
carry them as code, for editors and language servers (#291).

### Decimals in reports keep their scale

`verify`'s "known about the output" showed a decimal column's bound as its
internal unscaled integer: TPC-H Q6's `revenue` read "an integer ≥ 450000".
It now reads "a decimal(38, 4) ≥ 45.0000", with the column's type (#250).

### Dates: the reference's own range

Date arithmetic is now checked against the reference's dates, the SQL
standard's 0001-01-01 to 9999-12-31, instead of the (much wider) range
DataFusion computes. Adding days or months that leaves them raises "outside
the reference's dates" on every engine, and `verify` reports it. With
constant operands, such as TPC-H Q6's `DATE '1994-01-01' + INTERVAL 1 YEAR`,
the written SQL no longer carries a range check at all (#251).

### More divisors proved non-zero

`verify` now proves a divisor non-zero from more preconditions:
`(b < 0) | (b > 0)`, `(b != 0) | b.isnull()`, and a product `b * c` of
factors each known to be non-zero. Each needed a guard before.

### What DuckDB SQL lifts to is generated and proved

The Lean build now generates, for DuckDB's `/` (of integers and of doubles),
`%` of doubles, `log`, `sign`, `greatest` and `least` (which skip NULLs) and
casts between BIGINT and DOUBLE, and the aggregate `avg` of BIGINTs, the Substrait expression each lifts to under
`semantics="duckdb"` and `"reference"`, and proves it means what DuckDB's
function means (`SubstraitLean/DuckDBSQL.lean`, `LiftSearch.lean`). With
DuckDB's semantics, `±∞` and NaN results are stated exactly, as guarded
constants: `log(0)` is `-∞`, `x % 0.0` is NaN. `substrait-check --lift-table`
prints the table as JSON, for the SQL lift to read; a function the model
cannot state is listed as refused, with the reason (DuckDB's `CAST` of a double
to an integer rounds half to even)
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)).

DuckDB's `avg` of integers sums them exactly before dividing; with DuckDB's
semantics it now lifts to `CAST(sum(x) AS DOUBLE) / count(x)`, proved equal,
where Substrait's `avg` of doubles would round as it sums (values beyond 2⁵³).

### DuckDB's elementary functions and power lift exactly, and the lift has a cache

With `semantics="duckdb"`, `sqrt`, `exp`, `ln`, `log`/`log10`, `log2`, the
trigonometric functions and `power` now lift to what DuckDB computes, NaN and
`±∞` included (`sqrt(-1)` and `asin(2)` are NaN, `ln(0)` is `-∞`, a negative
base to a fractional power is NaN), each proved
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)). The
lift generator keeps a cache of the templates it found
(`SubstraitLean/LiftCache.lean`, regenerated with `substrait-check
--lift-cache`), tried first on the next build: a build with the cache takes
15 s where a search from scratch takes about 3 minutes. A template the search
does not reach can be seeded by hand there; it is still proved by the kernel.

### The SQL lift reads Lean's generated DuckDB lift table

With `semantics="duckdb"`, the SQL lift now writes what Lean's generated lift table says for each construct it covers (#268): `/`, `%` of doubles, `log`, `sign`, `greatest` and `least`, casts between BIGINT and DOUBLE, and `avg` of integers. Lean generates each entry and proves it means what DuckDB computes. `substrait-check --lift-table` exports the table, and the lift reads it from the checker sverify ships with.

The entries state NaN and ±inf exactly, as DuckDB computes them, instead of refusing them or raising:
- `%` of doubles is no longer refused: by zero, or of an infinity, it is NaN.
- `log(0)` is `-inf`, and `log` of a negative is NaN.
- `inf / inf` is NaN.

A contract that NaN or an infinity would break fails to prove, and one they can't break still proves. `avg` of integers is the exact sum divided by the count, in doubles, as DuckDB computes it.

The other constructs keep their hand-written rules until their entries are generated. The reference semantics is unchanged.

### Decimals

`DECIMAL(p, s)` columns, literals and arithmetic are verified, in Ibis and in
SQL (#27, #67). The reference computes them exactly: `+` and `-` at the
larger scale, `*` at the sum of the scales, and an overflow of the precision
is an error, which `verify` rules out from the columns' declared precision.
Casts to a smaller scale round half away from zero, to an integer truncate,
and to and from doubles round once. `SUM`, `MIN`, `MAX` and `AVG` work in
groups and windows; `AVG` is `DECIMAL(p + 4, s + 4)`, rounded half away from
zero. Division of decimals is refused. DuckDB runs decimal plans and
compensates where its own types or rounding differ
([engine profiles](../docs/engine-profiles.md)); Polars, Spark and Snowflake
refuse them for now.

### Chapter 16 of the tour folded into chapter 17

The tour's appendix on DataFusion's quirks (`16_datafusion_semantics.py`)
described DataFusion as the SQL frontend it no longer is (#211). Its parts
that still matter now live in chapter 17 (`17_backend_semantics.py`), as a
new section 8 on DataFusion as a backend: when DataFusion evaluates an
expression (E1–E5), and the soundness gaps found while sverify planned SQL
with DataFusion (D1–D11), each re-checked live against `verify` and the
model and ranked most severe first. Most of those gaps closed with the lift;
what remains is that DataFusion wraps integer overflow silently where the
model raises, which `verify` reports as `may fail: overflow`.
`catalogue/pitfalls.toml`'s `quirks` now name chapter 17's entries.

### DuckDB is the test oracle; the docs describe SQL as DuckDB SQL

The tests check the reference model and the engines against DuckDB, the Tier 1
engine, wherever they used to run raw SQL or Ibis's SQL on DataFusion as an
oracle. DataFusion keeps the tests about it as a backend: checked plans
running on it, and the native behaviours that motivate a refusal.
`sverify.engine.run_sql` (internal) is gone. Raw DuckDB SQL over a
connection's tables is `sverify.testing.duckdb_sql`, and an Ibis expression's
own DuckDB SQL is `sverify.testing.duckdb_ibis`. The coverage harness's
`DATAFUSION_SQL` and `NO_DATAFUSION_SQL` are replaced by one list,
`NO_DUCKDB_SQL`: the cases where DuckDB's own SQL computes something other
than the plan. `sverify.testing.parse_row` is private now (`parse_rows`
stays). The README, `python/README.md`, `docs/reference-semantics.md`, the
tour's chapters 12 and 14 and the agent skills describe SQL as DuckDB SQL,
read by sverify's lift with `semantics="duckdb"` or `"reference"`, and
DataFusion as an optional backend.

### Bounded state for time buckets: `arrives_within` and retention by watermark

`sv.arrives_within("ts", hours=2)` in `requires` bounds how late a source's
rows arrive. It is checked on every batch at refresh: a row before the
watermark (the largest `ts` seen minus the lateness), or a NULL, rejects the
batch. A node that aggregates by `ts.truncate(...)` or `ts.bucket(...)` then
drops the buckets that end at or before the watermark from its state once its
sink has written them, and keeps at most `⌈lateness / width⌉ + 1` open. Lean
proves that a final bucket's delta is empty for every admissible batch and the
bound (`SubstraitLean/Retention.lean`). The refresh report gives the open and
retired buckets and the bound. `DeltaSink` keeps the retired buckets
(`Sink.keeps_retired`); with other sinks the node keeps every bucket (#294).

### The last of DataFusion's SQL path is gone

sverify no longer monkey-patches Ibis's DataFusion SQL compiler: the two
patches (sub-second interval literals, integer `//`) changed Ibis for every
user of Ibis-on-DataFusion and served only the internal
`sverify.engine.to_sql`, which is removed as well. The one `to_sql` left is
`sverify.engines.to_sql`, which writes SQL from a checked plan. The query
catalogue runs each query on DuckDB itself rather than DataFusion
(`status.json` records it as `native`), and no longer asks DataFusion's SQL
planner whether a query plans.

### Integer division overflow at narrow widths

`MIN // -1` at TINYINT, SMALLINT and INTEGER (`-128 // -1` is 128, which a
TINYINT cannot hold) is now reported as an overflow, as it already was for
BIGINT, and the plans sverify writes raise there, as DuckDB does (#334).
Integer division at a narrow width is now checked at that width, like `+`,
`-`, `*` and negation. The sqllogictest replay also sees `verify`'s warnings
for queries that read no table, such as `SELECT 7 // 0` (#333): `verify`
reported those all along, but the replay's check went through
`sverify.sql`, which refuses such queries.

### `round(x, d)` at every number of digits

`round(x, d)` of a double now means what DuckDB computes for every `d`
(#335): below zero it divides by an exact power of ten and multiplies back,
so `round(42.0, -1000)` is 0, not NaN, and `round(521924.889, -5)` is
`500000.0`, not `499999.99999999994`. A result that would not be finite
falls back to 0 (for `d < 0`) or to `x` (for `d ≥ 0`). The plans sverify
writes now include `round` with digits for a double literal, which they
refused before ("unsupported function round/2"). DataFusion rounds
otherwise, so it refuses `round(x, d)` until #271.

### `substring` out of range is an error, and strings have fewer than 2³² characters

- The size hypothesis for strings is now 2³² characters (it was 2⁶²); relations
  a window reads keep 2⁶² rows (#336).
- `substring` with an offset outside `[-2³², 2³²)` or a length of `2³²` or more
  is an error in the reference semantics, as DuckDB raises. `verify` reports it
  as a domain error unless the offset's bounds rule it out, for columns and
  constants alike, and the written plans raise there on DuckDB and Polars. The
  lift no longer refuses such constants.

### GREATEST and LEAST check in linear time

`GREATEST(a, b, c, …)` and `LEAST(…)` used to be read as a chain of conditionals, each of which copied the one before. With ten arguments, the checker ran for minutes, and a plan written back held thousands of copies of each argument (#340). They're now one operation per pair, `BinFn.greatest`/`least`, which `Expr.eval_greatest` proves is the conditional it replaces. Thirty arguments check in well under a second.

The contract checker keeps its precision. `GREATEST(x, 0)` is still known to be at least 0, and Ibis's `clip` to stay within its bounds; `pickAbs` is proved sound. Written plans carry `greatest`/`least` as single calls, run natively:
- DuckDB, Spark and DataFusion: their own `GREATEST`/`LEAST`, which skip NULLs;
- Snowflake: `GREATEST_IGNORE_NULLS`;
- Polars: the same comparison as before, now one step per pair.

Greatest and least of lists are written as the conditional, as before.

### Set operations in SQL

DuckDB SQL with `UNION`, `EXCEPT` and `INTERSECT`, each with or without `ALL`,
now verifies, in subqueries and CTEs too, with `ORDER BY` and `LIMIT` over the
whole operation (#344). The branches meet at DuckDB's common column types, and
take the first branch's names. NULLs count as equal, and with `ALL`, `m` and
`n` copies of a row leave `min(m, n)` (`INTERSECT ALL`) or `max(m − n, 0)`
(`EXCEPT ALL`), as in DuckDB. DuckDB's `TABLE t` shorthand, which SQLGlot does
not parse, is written out as `SELECT * FROM t` first. In the sqllogictest
replay, the `setops` area went from 18 agreeing queries to 79, none disagreeing.
`UNION BY NAME` is still refused.

### Windows over every column are deterministic

A window partitioned by every column of its input, such as
`ROW_NUMBER() OVER (PARTITION BY` every column`)`, is now reported as
deterministic without a key. Rows tied in such a partition are equal, so how
an engine breaks the ties cannot change the result (`window_allColumns`,
proved). So `INTERSECT ALL` and `EXCEPT ALL`, which number the copies of each
row this way, are deterministic too, with or without keys on their inputs.

### Lists in DuckDB SQL: literals, indexing, UNNEST

The SQL lift reads DuckDB's list literals (`[1, 2, 3]`, nested ones too),
`l[i]` with a constant index (from 1, from the end for a negative `i`, NULL for
`0` and out of range), and `UNNEST(l)` in the select list (one row per
element, none for a NULL or empty list) (#348). Lean's results match DuckDB's.
DuckDB's SQL writer has no lists yet (#94), so these plans are checked against
DuckDB's own result but not run back; the sqllogictest ledgers now count such
agreements apart ("Oracle A only"). Lists of computed elements, of DECIMALs,
slices and an untyped `[]` are refused with a reason.

### Contracts on rollups: `MIN`, `MAX` and `AVG` of a group

More of a rollup's contract is proved before any data runs.

- `MIN` and `MAX` of doubles are accepted (#371). DuckDB orders doubles as
  the reference does, `-∞ < … < +∞ < NaN`; Polars and DataFusion refuse them
  until #271.
- `MIN`, `MAX`, `AVG` and `SUM` of a column that is never NULL, over a group
  without a filter, are never NULL (#372).
- `MIN ≤ MAX` for measures of the same values on one group, and an integer
  `AVG` with an integer result lies between them (#372).
- A decimal `AVG` and an integer `AVG` with an integer result lie within their
  values' bounds (#237). TPC-H Q17's `0.2 * avg_qty` is now proved not to
  overflow.
- A conversion of integers to doubles keeps their bounds: `CAST(x AS DOUBLE)`
  of `x` in `[0, 1000]` is in `[0.0, 1000.0]`.

An `AVG` of doubles, including the mean of integers as a double, rounds and
can step past its values (the mean of three `0.1` is `0.10000000000000002`),
so it gets no bound from its inputs here. Error bounds for it come with #85.

### Runtime-checked postconditions on nodes

`on_unproved="runtime"` now works on nodes built from sources (#373). The
postconditions Lean could not prove are checked at every refresh, on the full
result the first time and then on the rows each batch inserts (keys on the
new state), before the sink commits. A violation raises `PostconditionError`
and the refresh writes nothing. Before, building such a node raised
`VerificationError`. The transform's report marks these postconditions as
checked on data (`CheckedCondition.checked`), and the refresh report lists
them as `ensures` lines next to the preconditions. Downstream transforms
assume only proved postconditions, so a node with checked ones is stored with
`.write` before another transform reads it. An incremental view of an eager
result checks them on every batch too.

### Custom sources resume from the cursor their sink recorded

A sink now records the cursor of each source next to its version
(`Contract.cursors`). A `sverify.io.Source` that implements
`restore(cursor)`, the whole table as of a recorded cursor, starts there
after a restart: the stored nodes resume from their sinks, the first
refresh reads only what is new since, and the sink writes that change.
`from_query`, `from_files` and `FlightSource` implement it. A source without `restore`, or
whose cursor is gone (`restore` returns None), is read in full again and
written once, as before. `Source.snapshot` also serves the versions whose
batches the source still keeps (#374).

### Arrow Flight sources

`sverify.io.flight.FlightSource` reads a table of a numbered batch log on an
Arrow Flight server: each refresh streams the batches after the last one
read, registers them with the engine without a copy, and reads the batches
the server dropped past its retention as deletes. `FlightLog` is a small
in-memory server for that log, and the [guide](docs/guide.md) documents the
protocol for other servers. `pip install 'sverify[flight]'` (#375).

### A source with `schema=` proves contracts without reading

`Source.schema()` returns the schema given as `schema=` without reading the
source, so building a node proves the transform's contract whatever the state
of the source, and the first read happens at the first refresh (#376).

### Delta sinks maintain their tables and resume past maintenance

`DeltaSink` takes `checkpoint_interval`, `log_retention`, `compact_every`
and `vacuum_retention`, and `DeltaSink.maintain()` compacts and vacuums by
hand. The maintenance commits carry the contract of the sink's last commit.
A restarted job now resumes from a table whose commits after the sink's
last one change no rows: `OPTIMIZE`, `VACUUM`, property and constraint
changes, by `maintain` or another writer. It used to recompute the node and
overwrite the table. An Iceberg sink resumes past `replace` snapshots
likewise (#377).

delta-rs 1.6.6 hangs in `history()` and `set_table_properties()` against an
S3 server in the same Python process, such as moto's `ThreadedMotoServer`
(`upstream/LEDGER.md` DL-1). Run moto as its own process.

### One-line refresh summaries

`Refresh.summary()` gives one line per node for the log of a job that
refreshes often, such as "paid: orders@v1→v2, Δ trusted (change feed),
requires checked on 1 row(s) (3 proved from metadata), merge v3: +1 −0"
(#378). Postconditions a node checks on its output (`on_unproved="runtime"`)
show as "2 ensures checked on data", and a node's time buckets (#294) as
"bucket: 3/3 bucket(s) open, 1 retired". `str(refresh)` keeps the full report. A node's line becomes its full
entry when the refresh did something notable (`StageRefresh.notable`): its
first refresh, a source recomputed without a change feed, a schema change
(`SourceRefresh.schema`), or a sink overwriting its table.

### Overflow hints name the bound to add

A report's overflow hints now name the column and propose bounds (#379),
in `Report.hints` and as `hint:` lines. A truncated or binned timestamp or
date gets a lower and an upper bound on its column, such as
`_.ts >= datetime(2000, 1, 1)` and `_.ts < datetime(2100, 1, 1)`, which clear
the overflow. An integer `SUM` that is checked while the job runs gets the
range Lean knows for the column it adds up and the largest group whose sum
then fits 64 bits, or, for an unbounded column, a bound to add and the group
size it allows. No contract can state a group's size, so the hint says so.
The general hint stays for overflows the new ones do not cover.

### GREATEST and LEAST of date and timestamp constants run as dates again

`LEAST(DATE '1992-01-01', DATE '1991-01-01')` and its timestamp counterpart returned the integer code of the result on DuckDB (`7670`, `662693025000000`), whenever every argument was a constant (#381, a regression of #355). The plan Lean writes back now writes two constants in the call's own kind, as it does elsewhere, so they are dates and timestamps to the engines. Lean's own results were right throughout.

### TIME constants, substring ranges and retention under a projection

- `TIME '13:45:21'`, `CAST('…' AS TIME)` and a string compared with a `TIME`
  column now lift to a TIME literal, so queries that compare a `TIME` column
  with a constant verify. Constants DuckDB raises on, and `24:00:00`, are
  refused (#386).
- `substring` with a constant offset outside [-2³², 2³²) or a constant
  length of 2³² or more is refused: DuckDB raises there, and the model has
  no such error yet (#336).
- Retention engages for an aggregate under a filter or a projection, such as
  a per-mille-to-percent `select` after the `aggregate` (#394).

### `arrives_within` lets a source's own retention through

A delete before the watermark no longer rejects the batch when its row is in
a bucket every retiring view has made final: it is the source's own
retention, such as a `FlightSource` floor or a Delta `VACUUM`. The views and
their sinks keep those buckets, and the report counts the expired rows. Lean
proves the result is the full recompute over the rows the source received
(`Retention.expiry_sound`). A delete before the watermark in a bucket that is
still open rejects the batch (#395).

### Clearer contracts API and messages

- A `requires` key that names no input raises a `ValueError` naming the key,
  the inputs and a close match, where it raised a bare `KeyError`. A
  transformation with one input takes a plain list,
  `requires=[_.amount >= 0]` (#408).
- `@sv.transform(infer=False)` turns off bound inference, as on `sv.verify`.
  `strict=True` still works and warns that it is deprecated (#409).
- `sv.references("cust", to=customers.id)` names the referenced column with
  an Ibis column or a `(table, column)` pair. The positional form
  `references(col, table, other)` warns that it is deprecated (#412).
- `Connection.datafusion` is deprecated: the DataFusion session is an
  internal of the DataFusion engine (#413).
- Refusals give their reason in terms of the reference semantics, with the
  issue to follow and a workaround, and no longer cite DataFusion's
  behaviour (#410).
- An unproved condition says why in words: "it may be FALSE on some rows",
  and where it may be NULL, how to declare the column NOT NULL. This
  replaces "(it is TRUE or FALSE)"; `CheckedCondition.why` has the text
  (#176).

### The reference semantics is the default everywhere

Breaking: `sv.sql(query)` now uses sverify's reference semantics by default,
as `sv.verify` and `@sv.transform` do; DuckDB's semantics (NaN and ±inf as
DuckDB computes them) is an explicit opt-in, `semantics="duckdb"` (#411).
Write `semantics="duckdb"` on `sv.sql` calls that relied on the old default.
SQL transformations and SQL conditions in `sv.verify` and `@sv.transform`
were lifted with DuckDB's semantics too, and now follow the new `semantics=`
parameter of each, which defaults to the reference. `Report.semantics`, and a
`semantics:` line in the printed report, say which semantics a check used.

### Narrow arithmetic on constants keeps its width

In `(10::TINYINT * 10::TINYINT) * x`, the parser treated the inner product as
a 64-bit value because it reads no column, so the outer multiplication was
not checked at 8 bits: `verify` missed the overflow and the written plan
returned 1000 where DuckDB raises. A call's declared output type now gives its
width (#419), as a column's does, at TINYINT, SMALLINT and INTEGER and for
`+`, `-`, `*`, negation and division.

### Inferred bounds on eager tables

`@sv.transform` on an eager table (an `ibis.memtable`, or any plain Ibis
expression that is not a contracted result) now infers the bounds that rule
out overflow, checks them on the table's data, and proves the contract, as
`sv.verify` does. Hints name the bound as a `requires` of the parameter
([#430](https://github.com/AlexanderNenninger/substrait-lean/issues/430)).

### Fixed: `avg` of a nullable integer under `semantics="duckdb"`

An `avg` of an integer column that may be NULL failed its proof with
"division by zero", because DuckDB's `avg` is lifted as the sum divided by
the count, and the count of a group whose values are all NULL is 0. The lift
now states that such a group's average is NULL, as DuckDB returns it, so
nothing can fail (#434).

### Fixed: reports on a DATE beyond the year 9999

A transformation with a DATE column whose range passes Python's limits, such
as `CAST(ts AS DATE)` of a TIMESTAMP, raised `OverflowError` while describing
its facts. Bounds outside the years 1 to 9999 now go without saying: the
column is "any date" (#435).

### A transformation with an `ibis.param` says how to bind it

A contracted transformation whose body uses an `ibis.param` failed with a
bare `KeyError` from Ibis. It now raises a `TypeError` naming the parameter:
transformations don't bind parameters yet (#354), so prove the expression
with `sv.verify(expr, params={param: value})` or write the values as
`ibis.literal(...)` (#440).

### Fixed: Ibis's DuckDB `create_table` failed on a fresh install

A fresh install resolved SQLGlot 30.18 or later, from which SQLGlot reads a
`DROP`'s names where Ibis 12 doesn't put them, so `con.create_table(...)` on
Ibis's DuckDB backend raised a DuckDB syntax error. sverify now requires
`sqlglot~=30.17.0` until Ibis follows
([upstream/LEDGER.md](../upstream/LEDGER.md) SG-7, #442).

### Fixed: SQL reports described timestamps and dates as integers

The facts of a SQL transformation described its timestamp and date columns
as "any integer", the model's codes for them. They now read as the same
columns written in Ibis do, "any timestamp" and "a date in [...]" (#452).

### Numeric functions: `sqrt`, logarithms, trigonometry, `sign`, bitwise operations

Ibis's `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `atan2`, `cot`, `degrees`, `radians`, `sign`,
`isinf`, `e` and `pi`, and the bitwise `&`, `|`, `^`, `~` and shifts, are
verified (#48). The functions compute as C's libm does, and contracts treat
their results as doubles. Outside a function's domain (`sqrt` of a negative,
the logarithm of 0, `asin(2)`, `atan2(0, 0)`, a shift by more than 63) the
reference raises a domain error, which `verify` reports unless a filter or
`requires` rules it out: `t.filter(_.x > 0).select(_.x.ln())` is proved.
DuckDB and Polars run them all; Spark runs `sqrt` and the bitwise operations,
Snowflake `&`, `|` and `^`, and both refuse the rest.

### Regular expressions and digests

Ibis's `re_extract` and `re_replace` (DuckDB's `regexp_extract` and
`regexp_replace`, with or without the flag `'g'`) and `hexdigest('md5')` and
`hexdigest('sha256')` are verified on DuckDB (#50). Patterns must be
constants in the subset `Text.simpleRegex` accepts, which now includes
non-capturing groups `(?:…)`. Proofs treat these functions as black boxes,
but Lean evaluates them: regular expressions with RE2's leftmost-first
matching and DuckDB's edge cases (`''` where nothing matches, `\1` in the
replacement, empty matches), and the digests as lowercase hex. So
ClickBench Q28 and dbt's surrogate key now verify. DuckDB's `hash()` and
Ibis's URL parts (`host()`, …) are refused, and the other engines refuse
all of these until #271. The DuckDB SQL of `\b` in a pattern now raises on
non-ASCII text, as `\d`, `\w` and `\s` already did, since RE2 and Rust
disagree there.

### `any()` and `all()`

Ibis's `any()` and `all()` of booleans are now verified, as `MAX` and `MIN`
(`BOOL_OR` and `BOOL_AND`): NULLs are skipped, and a group without a
non-NULL value gives NULL (#53).

### Bit aggregates

`bit_and()`, `bit_or()` and `bit_xor()` of integers are verified: the
64-bit operation folded over the non-NULL values, NULL for a group without
one. They run on DuckDB, Polars, DataFusion, Spark (`BIT_AND`, …) and
Snowflake (`BITAND_AGG`, …) (#53).

### Covariance and correlation

Ibis's `cov()` and `corr()` (DuckDB's `COVAR_SAMP`, `COVAR_POP` and `CORR`)
are verified on DuckDB, grouped, with DuckDB's own algorithm (#54). `CORR`
is NULL for fewer than two pairs and where one side's values are all equal,
as the SQL standard says, rather than DuckDB's NaN, and an infinite value
raises, since a deviation from the mean would be NaN. The other engines refuse
them until #271.

### Variance and standard deviation

`var()` and `std()` of doubles and integers, of a sample or a population
(`how="pop"`), are verified on every engine (#54). Each engine uses its own
algorithm for now, so results may differ in the last bits, and a contract
can rely only on the value being a non-negative double, or NULL: for no
values, and for a sample of one value. A NaN passes through; an infinite
value raises, since its deviation from the mean would be NaN. Variances over
windows are refused.

### `distinct(on=)`, and `first()`/`last()` without an order

Ibis's `distinct(on=…)` and `first()`/`last()` without `order_by` (DuckDB's
`FIRST`/`LAST` with no `ORDER BY`) are now verified rather than refused
(#55). They take any row's value, so the report says the result is not
`deterministic`, and proves nothing about it, unless the grouping (`on`)
columns form a key. Each column is chosen on its own: `distinct(on="name")`
may keep `a` from one row and `b` from another, so a fact about every input
row, such as `a <= b`, need not hold of the result. They run on DuckDB for
now; the other engines refuse them until #271.

### `first()` and `last()` with an order

Ibis's `first(order_by=…)` and `last(order_by=…)` (DuckDB's `FIRST(x ORDER
BY …)`) are verified: the first or last non-NULL value in that order, NULL
without one (#55). Without `order_by` they are any row's value and stay
refused. Where rows tie in the order, the report says the result is not
`deterministic`, unless the grouping and order columns form a key. They run
on DuckDB for now; the other engines refuse them until #271.

### `group_concat()` with an order

Ibis's `group_concat(sep, order_by=…)` (DuckDB's `STRING_AGG(x, sep ORDER
BY …)`) is verified: the non-NULL strings in that order, joined by a constant
separator, and NULL without values (#55). Without `order_by` the order is
the engine's, so it stays refused. As for `first()` and `last()`, rows that
tie in the order make the report not `deterministic` unless the grouping and
order columns form a key. It runs on DuckDB for now; the other engines refuse
it until #271.

### `ibis.param` values for `verify`

`sverify.verify` takes `params={param: value}`, as Ibis's
`execute(params=...)` does, and binds each `ibis.param` to its value before
compiling (#58). The report is about the expression with those values, and
says so: `Report.params` lists them, and the report notes that its proofs
hold for those values only. A parameter left unbound is still refused, now
with a reason that says to pass `params`.

### Refusals say why

`random()`, `uuid()`, `now()`, `today()`, `typeof()`, `ibis.param` and
`try_cast` were refused with "X is not supported". The message now gives
the reason and what to do instead, for example to pass the time in as a
column or constant (#58).

### `try_cast()`

Ibis's `try_cast()` (Substrait's `failureBehavior: RETURN_NULL`, SQL's
`TRY_CAST`) is verified for a double to an integer and an integer to a
narrower integer (#58): NULL where `cast()` would raise, so `verify` reports
no "cast out of range" for it. A double still truncates toward zero, as the
reference's `cast()` does, where DuckDB's own `TRY_CAST` rounds. `TRY_CAST`
to a DECIMAL, of a DECIMAL to an integer, and of strings is refused. It runs
on DuckDB for now; the other engines refuse it until #271.

### Casts of rounded aggregates keep their bounds

With a row cap (`sv.max_rows`), a cast of a `SUM` or `AVG` of doubles keeps
the aggregate's proved error bound (#85, #223). `CAST(AVG(cpu) AS BIGINT)` of
`cpu` in `[0, 100]` is in `[0, 100]`, and `verify` no longer reports that the
cast may fail, nor a cast to a decimal that the bound keeps within its
precision. A `SUM` of integers cast to doubles carries each conversion's
rounding in its bounds.

### Contracts on `SUM` and `AVG` of doubles, up to rounding

Rollups of doubles get proved bounds (#85).

- `sv.max_rows(n)` caps an input's rows, checked on the data. With a cap, a
  `SUM` or `AVG` of doubles in `[lo, hi]` is bounded by the exact result's
  interval widened by the proved rounding error (`docs/float-bounds.md`).
- `sv.approx(cond)` states a postcondition up to that rounding:
  `sv.approx(_.cpu_avg <= 100)` is proved where `_.cpu_avg <= 100` is not,
  and runs as `_.cpu_avg <= 100.0001`. A report hints at it when an exact
  claim fails only by rounding.
- Signs are exact without a cap: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`.

### Proved error bounds for floating-point aggregates

The `float-bounds/` package proves error bounds for `SUM`, `AVG`, `VAR_*`,
`STDDEV_*`, `COVAR_*` and `CORR` of doubles (#85), in the standard model of
rounding with its underflow term. A sum of `n` values is within
`γ n · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact one, sequentially or in shards; the
co-moment behind the variance family is within `64 · n² · u · B²` for each of
the two-pass, textbook and Welford/Chan algorithms (DuckDB's), so the bound
holds whatever an engine uses. See `docs/float-bounds.md`.

### Generic properties of statistical aggregates

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` now have proved generic properties
that any common algorithm keeps (#85): `NULL` where the reference says, a
variance `≥ 0`, the result within `(128 n² u B² + 12 n u B²) / d` of the
exact one, and `|CORR| ≤ 1 + ε` when both variances are bounded below. The
reference allows any result with them (`StatProps`), so DuckDB's Welford,
Polars' blockwise two-pass and the reference's own two-pass all agree with
it. Engine profiles can name a stricter algorithm (`Profile.statAlgo`).
A computed double's bound now carries through `CAST(x AS BIGINT)` with row
caps, and `SUM(CAST(x AS DOUBLE))` of integers gets the summation bound.
See "Statistical aggregates" in `docs/reference-semantics.md`.

### Statistical aggregates within bounds that scale with the spread

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` may now differ from the exact result
only by bounds that scale with the spread of the values (`StatProps`,
`docs/reference-semantics.md`). For `10⁶` values near `10⁶` that vary by about
`1`, the variance is within about `2 · 10⁻²`, where the earlier bound allowed
`1.4 · 10⁴`. The bounds are proved for two-pass and for DuckDB's algorithm;
the textbook formula `Σx² − (Σx)²/n` falls outside them.

### Variance bounds that scale with the spread

`float-bounds/` proves tighter variance bounds for three algorithms (#85):
two-pass, Lean's own, is within `8 n u S + 80 n² u² Σx²` of the exact sum of
squared deviations `S`, Welford's update within one thread within
`32 n u √(S Σx²) + 104 n² u² Σx²`, and DuckDB's parallel aggregation (Welford
in each thread, Chan's merge with a fused multiply-add) within
`148 n u √(S Σx²) + 3961 n² u² Σx²`. The covariance has the analogues, for
two-pass and for DuckDB's parallel aggregation, in `√(S_xx S_yy)`,
`√(Σx² S_yy)` and `√(Σy² S_xx)`. They stay useful for values far from zero
with a small spread, where the generic bound does not. The
standard model of rounding now states that a double rounds to itself.

### Lists run on DuckDB

Plans with lists now run on DuckDB as well as Polars (#94): list columns and
literals, list elements and `length`, `collect()` (ordered or not, NULLs
skipped) and `unnest`. The written SQL keeps Lean's order: each row's
elements come out in list order, and ties in a `collect` order fall to the
row order, so an order-dependent step above sees the same rows Lean does.
Snowflake and Spark still refuse lists, until #271; structs and lambdas stay
Polars-only for now.

### Struct fields, list elements and lambdas

Ibis's struct fields (`t.s.a`), list elements (`t.l[0]`, a constant index,
negative from the end), `length()` of a list, and `map`, `filter` and
`contains` on lists are verified (#94). A lambda may read only its element
and constants, so `contains(v)` needs a constant `v`. A NULL element matches
only NULL in `contains`. `verify` reports an error in a lambda's body on any
element as the row's. Polars runs them; for DuckDB, see "Lists run on
DuckDB". This also fixes the Ibis producer reading `t.select(a=t.s.a)`
as the table's first column.

### A batch updates a source table at the cost of the change

Applying a batch to a pipeline's copy of a source table no longer groups the
whole table. A batch of inserts appends them, and deletes touch only the rows
equal to a deleted row. On the metrics benchmark (2.4 million rows, one minute
of samples per refresh) this was about 200 ms of a 365 ms refresh.

### A stale checker fails with a clear message

`substrait-check --version` prints the checker's protocol, and sverify checks
it once per process: a checker older or newer than the package raises
`sverify.errors.CheckerVersionError`, which says how to rebuild it (`uv sync`
or `lake build substrait-check`), where a stale build used to fail later with a
`KeyError`.

### `inf - inf` and `0 * inf` are NaN under `semantics="duckdb"`

With DuckDB's semantics, `+`, `-` and `*` of doubles now lift to what DuckDB
computes: NaN for `inf - inf`, `-inf + inf` and `0 * inf`, as `/` already
gave for `inf / inf` and `0 / 0`. Lean's generated lift table states them
exactly (`DuckFn.addDouble`, `subDouble`, `mulDouble`), so the plan Lean writes
back runs on DuckDB and gives NaN too, where it used to raise "domain error".
The reference semantics still raises there (#257).

### Engine facts: JSON only, and an `io` layer

The facts in `characterization/<engine>/facts/` are the record: the generated
`FACTS.md` overviews, `python -m sverify_dev.facts --write` and their step in
the `Generated files` workflow are gone; `python -m sverify_dev.facts` checks the
documents. `fact.schema.json` has a layer and an area `io` (how an engine reaches
data: extensions, catalogs, object stores, credentials) and a status
`workaround`. The first: DuckDB's `unity_catalog` extension's ATTACH ignores a
named secret unless it names it (`duckdb-IO1`) and ignores the vended `endpoint_url`, so a
MinIO behind Unity Catalog needs DuckDB's `s3_endpoint` settings (`duckdb-IO2`);
its `delta` reader is then denied with the table-scoped keys (`duckdb-IO3`, open).

### A fast default test suite

`poe test` runs the fast Python tests on 2 workers: it leaves out the tests
marked `slow` (engine agreement on many queries, long streams, replays, and the
Spark tests) and runs a tenth of each Hypothesis test's examples (the `dev`
profile, `SVERIFY_PROFILE`). `poe test-all` and `poe qa` run every test with
the full counts, as CI does; CI splits the `core` tests into three shards
(`SVERIFY_SHARD`, `python/tests/conftest.py`).

### Nightly wheels

Each night, when `main` has changed, the Wheels workflow builds and tests the
wheels for every platform and publishes them as the rolling
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly),
versioned `<next minor>.dev<commits>+g<sha>`. Install them with
`uv add "sverify>=0.4.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly`
or `pip install --pre sverify --find-links …`; `python/README.md` has the
details. Each build's wheels stay on the release for 30 days, so a pinned wheel
URL works that long. They never go to PyPI.

### No more Intel macOS wheels

Wheels exist for Linux (x86_64, aarch64) and macOS on Apple silicon (arm64).
On an Intel Mac, pip and uv build `sverify` from the sdist, which needs
[elan](https://github.com/leanprover/elan).

### The tour is five notebooks

The tour has three workflows (duplicate payments, sensor alerts, an orders
mart) and two guides: contracts (chapters 4 to 8 merged) and pipelines and
engines (chapters 9 to 12 merged). The start page and the chapters on how it
works moved to `docs/how-it-works.md`. Chapter 17 is now
`catalogue/backend_semantics.py`.

### Windows over time frames recompute only the rows near the change (tested)

A node of window aggregates over bounded RANGE frames of one time column
(`range=(-ibis.interval(minutes=5), 0)`) recomputes only the output rows
whose frames a batch's rows fall in, from the input rows those frames read.
This strategy is tested, not proved: `status()` and the refresh summary say
"touched frames recomputed (tested, not proved)", and the lemma it rests on
is #458 (#294).

### Touched groups read only the touched time range

When one of an aggregate's group keys is a fixed-width time bucket
(`ts.truncate("m")`, `ts.bucket(...)`), recomputing the touched groups reads
the input through the range those buckets cover, so the engine skips the
other rows while it scans. The semi-join on the keys still picks the exact
rows, and a touched NULL bucket reads the whole input.

### Aggregates recompute only the groups a batch touches

A node that ends in a `GROUP BY` over an input with delta rules no longer
recomputes and diffs its whole result on every refresh. It takes the group
keys of the input rows the batch inserts or deletes, recomputes those groups
(a semi-join on the keys) and replaces their rows, for any measure: MIN, MAX,
AVG, COUNT, SUM and the rest. Lean proves the split
(`TouchedGroups.touched_sound`). `status()` and the refresh summary say which
strategy ran. Other nodes without delta rules are still recomputed and
diffed, and #248 stays the issue for delta rules of aggregates.

### Windows recompute only the partitions a batch touches

A node whose window functions share one `PARTITION BY` (with the partition
keys among its columns) recomputes only the partitions a batch touches, the
way an aggregate recomputes its touched groups. Lean proves it from
`windowEval_sharded` (`TouchedGroups.touched_window_sound`), for inputs
without ties on the partition and sort columns. Windows with different
partitions, or none, are still recomputed and diffed.

### `division_type: TRUNCATE` is accepted

A plan whose `modulus` states `division_type: TRUNCATE` was refused,
although the remainder already takes the dividend's sign. It is now
accepted; `FLOOR` is still refused, as the model does not compute it.

### `approx_nunique` is refused

Ibis's `approx_nunique()` was translated as the exact `nunique()`. Each
engine computes its own estimate, so no plan gives the same answer
everywhere; it is now refused, with a hint to use `nunique()` for the exact
count.

### Isthmus support removed

sverify no longer compiles SQL strings with Isthmus (substrait-java's
Calcite-based compiler). Its frontends are Ibis and SQL through sverify's
own producers (#211, #231). `sverify.engines.isthmus_json`,
`sverify.engines.SQL_PRODUCERS`, `sv.connect(sql_producer=...)` and the
`SVERIFY_ISTHMUS` variable are gone. SQL strings need the `datafusion` extra
until the SQLGlot frontend replaces DataFusion's producer.

### Maintainer tooling leaves the wheel

The coverage harness, the query catalogue, the fuzzers, DuckDB's
sqllogictest replay and the example pipelines (`sverify.coverage`,
`sverify.catalogue`, `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`,
`sverify.examples`) were internal, and only the tests and CI used them. They
now live in `python/tools/sverify_dev` in the repository and are no longer
installed with sverify: about 4,000 lines fewer in the wheel.

### Fixed: a sink kept another plan's rows after the plan changed

If you use 0.3.0 and change a node's transform while keeping its sink,
upgrade. The sink recorded which plan wrote each state, but only compared
the state's epoch (the sum of the source versions) when deciding what to
write. So a job restarted with a new plan, at source versions the sink had
already committed, skipped the write: the table kept the old plan's rows and
its contract, while the node held the new plan's state. On the next source
change it merged the new plan's change on top of the old plan's rows, and
the table was wrong from then on, without an error. This affected
`DeltaSink`, `IcebergSink`, `sink_from` and sinks of your own that override
`committed()`.

A sink whose last commit came from another plan (`Contract.plan` differs) is
now overwritten with the new plan's whole state, and the refresh reports the
write as `overwrite`. `DeltaSink` replaces the table's schema and drops the
CHECK constraints it added for the old plan that the new one does not prove,
then adds the new plan's in the commit that records the epoch, so a job
stopped in between writes the state again. `IcebergSink` replaces the
table's schema in the overwrite's transaction. Constraints that another
writer added still stop the write.

A table is affected if you restarted a job with a changed plan before its
sources moved on. If it has not written a change since, the first refresh
after upgrading overwrites the table. If it has, that MERGE recorded the new
plan, and the fix cannot tell the table is wrong: delete the table, or point
the sink at a new location, and refresh to write it in full.

### Fixed: a node without a contract is planned again after a schema change

A node of a plain function, such as `orders.pipe(lambda t: t.select(t.id))`,
counted as contracted, so a dropped column, or a column widened beyond what
its values used to fit, raised `SchemaError` instead of planning the node
again. It is now planned again and recomputed, and its sink is overwritten.

### Changed: no operation creates a NaN

A NaN in your data still passes through, but an operation on numbers no
longer makes one where IEEE would. `inf - inf`, `0 * inf`, `inf / inf`,
`fmod(inf, y)`, a negative number to a fractional power, `sin`, `cos` or
`tan` of an infinity, and a grouped double `SUM` or `AVG` of both `+inf` and
`-inf` now raise a domain error on DuckDB, Polars, Spark and Snowflake, and
`verify` reports "domain error" unless the plan rules it out. So a job with
no NaN in its inputs has none in its outputs. For double arithmetic on
columns `verify` cannot bound, add bounds such as `_.x < 1e300` and
`_.x > -1e300` to `requires`. Adding a constant, or a whole-number power,
needs none. A plan that asks for `on_domain_error: NAN` is refused, and
`on_division_by_zero: IEEE` still gives NaN for `0.0 / 0.0`, as it asks.
DataFusion still gives NaN where the others raise (#257).

### Fixed: `%` of doubles gave wrong values

A plan that takes the remainder of doubles, such as `x % 2.5`, passed the
check but was evaluated on the doubles' internal codes, so its values were
wrong (`7.5 % 2.0` came out as a 300-digit integer). It is now C's `fmod`,
as DuckDB, DataFusion and Spark compute `%`: the result has the sign of the
dividend (`-7.5 % 2.0` is `-1.5`), a NaN gives NaN, an infinite dividend
raises (see above), and an infinite divisor gives the dividend. The value is exact. A zero
divisor is an error, as for integers, so `verify` reports "division by zero"
unless the plan rules it out (`WHERE y <> 0.0`). The Polars translation gives
the same results, although Polars' own `%` takes the divisor's sign.
Substrait itself defines no `modulus` of doubles (#203).

Substrait defines no `modulus` of doubles, so plans now call sverify's own
`sverify_fmod` for it, which the Ibis producer and the SQL lift emit for `%`
of doubles and which DataFusion runs as its own `%`. sverify still reads the
`modulus` of doubles that DataFusion's producer writes (#256).

## 0.3.0 (2026-11-01)

### Licensed under the MPL-2.0

sverify now has a license, the Mozilla Public License 2.0; 0.2.0 and earlier
were published without one. You can use sverify in open and proprietary
products alike. If you distribute changes to sverify's own files, they stay
under the MPL. The vendored `ibis_substrait` stays under Apache-2.0.

### Nodes compose left to right with `.pipe`

A job now reads in the order its data flows
([#189](https://github.com/AlexanderNenninger/substrait-lean/issues/189)).
It adds to the API and changes nothing that exists.

```python
paid_orders = orders.pipe(paid).write(DeltaSink("lake/paid"))     # chain, then store
enriched = paid_orders.pipe(enrich, customers=customers)          # fan-in by keyword
regional = paid_orders.pipe(
    sv.sql("SELECT o.*, c.region FROM orders o JOIN customers c ON c.cid = o.cid"),
    customers=customers,
)                                                                 # SQL is a step
quick = orders.pipe(lambda t: t.filter(_.amount > 0))             # no contract
sv.group(paid_orders.pipe(daily_totals), enriched).refresh()      # fan-out
```

- `Node.pipe(step, /, **inputs)`, and `pipe` on every source in
  `sverify.io`, apply a step to the node: the chained node fills the step's
  first table parameter, and the other inputs come by keyword. It builds the
  same node and plan as the call form `paid(orders)`, which stays public.
  A missing, duplicate or unknown input raises `TypeError` naming the step's
  parameters.
- A step is a contracted transform, a plain function from Ibis tables to an
  Ibis table (a transform with no contract), or `sv.sql(query)`.
- `sv.sql(query, *, as_=None)` without tables is a step whose inputs are the
  tables the query reads (not its CTEs, and each once). The keyword inputs
  bind their own names, and the chained node binds to the one table left
  over. A table with no input, an unused chained node, a keyword the query
  doesn't read, or an `as_` that isn't the table left over raises
  `TypeError`. `sv.sql(query, orders=orders)` inside a transform is
  unchanged.
- The README, the tour and the API reference lead with `.pipe`.

### Your own sources and sinks

Writing a source or a sink no longer means knowing sverify's internals
([#156](https://github.com/AlexanderNenninger/substrait-lean/issues/156)).

- `sverify.io.Source`: implement `read(since)`, which returns new rows and a
  cursor as a `Batch` (`kind="append"`, `"snapshot"` or `"changes"`).
  sverify numbers the reads as versions, keeps the table, and hands nodes
  the exact change. The refresh report says what the batches assume, and
  `refresh(audit=True)` reads the table again in full to check it, also
  when no batch arrived. `from_query(fn, cursor_on=...)`, `from_frame(fn)`
  and `from_files(path)` build one.
- `sverify.io.Sink`: implement `write(change)`, which gets a `SinkChange`
  (rows added and removed, or the whole table, and the contract), and
  optionally `committed()`. Exactly-once skipping and contract recording
  happen once, in the base class. `sink_from(fn)` hands the whole table to
  a function. Nodes reading a stored node of your own sink read what was
  written, with its exact changes. `DeltaSink` and `IcebergSink` are now
  subclasses, and every sink reports a `SinkWrite` (new mode `"update"`;
  `version` may be None).
- The full protocol for table formats is public as
  `sverify.io.VersionedSource`, with `Snapshot` and `SourceBatch`, whose
  `unchanged`, `from_changes` and `from_snapshot` build what `changes`
  returns. `Pipeline` no longer special-cases `StaticSource`: any source
  with a `digest` gets it recorded.
- `sverify.io.Storage` holds object store options shared by several tables:
  a mapping, or a function returning fresh options whenever a table is
  opened, so expiring tokens renew; `repr` shows option names only.
  `DeltaSource` and `DeltaSink` take one, or a function, as
  `storage_options`.
- A sink's `app_id` now defaults to `sverify:<sink name>` (it was the
  node's name, which is the same unless it clashed with a source's).
- `Contract.from_json` ignores fields it does not know, so contracts can
  gain fields without breaking the readers of this version.

### A pytest plugin for transforms and contracts

`sverify.testing` is now public
([#180](https://github.com/AlexanderNenninger/substrait-lean/issues/180)), and
installing sverify registers a pytest plugin (the `pytest11` entry point
`sverify`, off with `-p no:sverify`).

- `assert_contract(node)` asserts that every contract in a node's lineage is
  proved. With `data=` it runs the node on those rows: test data that breaks
  a precondition is reported with its rows, the output is checked against
  the postconditions, and with `expected=` it is diffed against the expected
  rows (missing and unexpected rows, as bags).
- `assert_engines_agree(node, data)` runs the node on every installed engine
  and diffs their results.
- `cases(node, max_rows=5)` is a Hypothesis strategy of input tables that
  meet a node's preconditions, for property tests of the code around it.
  It needs the new `testing` extra (`pip install 'sverify[testing]'`).
- The fixtures `sv_source(rows, schema, name=...)` (an in-memory source,
  also `sverify.testing.source`) and `sv_engine`, which runs a test once per
  installed engine (`installed_engines()`), or per engine of
  `--sv-engines=duckdb,polars`.

`python/tests/test_plugin_example.py` is an example test file, and
`python/tests/test_tour.py` tests the tour's transforms with the plugin.

### Ibis string functions

More of Ibis's string API is checked and runs on every engine
([#49](https://github.com/AlexanderNenninger/substrait-lean/issues/49)):
`lpad`/`rpad`, `repeat`, `reverse`, `replace`, `ilike`, `ascii`,
`levenshtein`, `right`, `find` with a start, `join` (`concat_ws`),
`find_in_set`, `capitalize` and slices. Each has the meaning of Ibis's
DataFusion SQL, by code point. A `repeat` past 2³¹ − 1 bytes is an
`overflow` error, which the checker rules out for a constant string with a
bounded count.

- Polars computes all of them exactly. DuckDB, Snowflake and Spark raise
  "non-ASCII text differs between engines" for `reverse`, `ascii`,
  `levenshtein` and `ilike` on non-ASCII text, and refuse `replace` with an
  empty pattern.
- `translate` is refused: DataFusion translates grapheme clusters.

### Fixes

- Written plans keep a projected literal's declared type: doubles,
  timestamps and typed NULLs no longer come out integer-typed
  ([#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96)).
- The tour notebooks declare the extras they use (`sverify[datafusion]`,
  `sverify[datafusion,polars]`), so they run in their own sandbox, as molab
  runs them
  ([#197](https://github.com/AlexanderNenninger/substrait-lean/issues/197)).

## 0.2.0 (2026-11-01)

A new public API, built around transforms that compose
([#164](https://github.com/AlexanderNenninger/substrait-lean/issues/164)).
It is a clean break: the old names are gone, with no deprecated aliases. The
proofs, the Lean model and what each engine computes are unchanged.

### Transforms compose; there is no pipeline object

```python
import sverify as sv
from sverify.io import DeltaSink, DeltaSource

orders = DeltaSource("s3://lake/orders")
p = paid(orders).write(DeltaSink("s3://lake/paid"))      # stored, and a source downstream
r = revenue(p).write(DeltaSink("s3://lake/revenue"))

r.refresh()                    # DuckDB in memory by default
r.refresh(engine="polars")     # or "datafusion", "spark", a Spark session
r.to_arrow(); r.to_polars(); r.to_pandas(); r.table
```

- A contracted transform (`@sv.transform`) called on a source or a node
  builds a `Node`. The contract is checked when the node is built: a link
  whose upstream guarantees don't imply the downstream assumptions raises
  `CompositionError` at once. Called on Ibis tables, a transform still
  returns an Ibis expression.
- Without a `.write` between transforms, they fuse into one plan and one
  incremental view, and the intermediate rows are never stored.
- `.write(sink)` stores a node, in the middle of a job or at its end, exactly
  once per state. It returns a node that downstream transforms read as a
  versioned source (Delta's Change Data Feed, Iceberg's snapshots), building
  on the contract its own stage proved.
- `refresh()` on any node brings its whole lineage up to date, upstream
  first, refreshing every node once per call and writing every stored node
  once. A restarted job rebuilds the same nodes; the first refresh resumes
  each stored node from its table.
- The engine is chosen at refresh time, not when the job is built.
  `"spark"` and Spark sessions are new as engines for maintained results.
- `sv.group(a, b).refresh()` refreshes several outputs against the same
  source versions and shares the stored nodes they read; `.status()` reports
  on each.
- `node.plan` is the plan Lean checked, for `sverify.engines`.

### SQL models

A transform's body can be SQL over its inputs, by keyword name:

```python
@sv.transform(requires={"orders": ["amount_cents >= 0"]}, ensures=["revenue_cents >= 0"])
def revenue(orders):
    return sv.sql("""
        SELECT region, coalesce(sum(amount_cents), 0) AS revenue_cents
        FROM orders GROUP BY region
    """, orders=orders)
```

`sv.sql(query, **tables)` returns an Ibis table, so a SQL model is an
ordinary node. It fuses with its neighbours, can be stored with `.write`,
composes with Ibis transforms on either side and reads several inputs. Its
schema and plan come from DataFusion's SQL producer, or Isthmus's without
DataFusion, and work on the placeholder tables nodes are built from. A query
the producer can't plan, or a plan Lean refuses, raises `Unsupported` saying
which part; without either producer the error names the `datafusion` extra.

### A small namespace

`import sverify as sv` holds eleven names: `transform`, `sql`, `verify`,
`unique`, `references`, `Report`, `Changes`, `group`, `connect`, `asof_join`
and `Node`. Three submodules hold the rest:

- `sverify.io`: `DeltaSource`, `DeltaSink`, `IcebergSource`, `IcebergSink`,
  `SinkWrite`, `Contract`, `StaticSource`.
- `sverify.engines`: running plans, SQL dialects and plan tools.
- `sverify.errors`: the exceptions.

Every other module (`sverify.incremental`, `sverify.contracts`,
`sverify.engine`, `sverify.sql`, `sverify.partition`, the per-engine modules,
`sverify.ibis_substrait`, `sverify.catalogue`, `sverify.coverage`,
`sverify.fuzz`, `sverify.testing`, `sverify.counterexample`,
`sverify.display`, `sverify.examples`, `sverify.io.delta`,
`sverify.io.iceberg`) is internal and may change in any release.

### Other changes

- Sinks no longer take a view: `DeltaSink(uri)`, `IcebergSink(catalog,
  identifier)`, attached by `node.write(sink)`. There is no public
  `sink.write()`: refresh writes. Delta and Iceberg sinks report through one
  type, `SinkWrite` (it replaces `IcebergWrite`).
- Sources and sinks take `name=`, the table's name in the plans that read
  them. It defaults to the last part of the URI or identifier.
- `StaticSource.apply(sv.Changes(...))` changes some rows of an in-memory
  source; the next refresh gets exactly that change, where `replace` makes
  it diff the whole table. `StaticSource` takes `name=`.
- A node without delta rules (left join, aggregate, window, `DISTINCT`,
  `LIMIT`) is recomputed and diffed, as views were inside a `Pipeline`. The
  standalone `IncrementalView`'s refusal (`NotIncremental`) is no longer on
  the public path.
- Incremental views over SQL strings become transforms whose body is
  `sv.sql(...)`.
### Fixes

- Arithmetic on double literals (`3.0 / 2.0`, a `CASE` of double literals
  plus `1.0`) used the integer operators on the literals' codes, which gave
  false proofs; the parser now reads a double literal, a cast to a double or
  such a `CASE` as a double
  ([#97](https://github.com/AlexanderNenninger/substrait-lean/issues/97),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- Booleans are ordered FALSE < TRUE, as DataFusion orders them; `b < TRUE`
  was NULL in the model
  ([#154](https://github.com/AlexanderNenninger/substrait-lean/issues/154),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- A bare double literal (`SELECT 1.5 AS c`) is written as an `fp64` literal,
  not as an integer holding its code, and `substrait-check` prints such a
  column as doubles. `0.0` and `CAST(NULL AS DOUBLE)` still come out with an
  integer column type (part of
  [#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96),
  [#166](https://github.com/AlexanderNenninger/substrait-lean/pull/166)).
- A `DeltaSink` refused its second write when a guarantee had parentheses
  that Delta drops when it stores a CHECK constraint
  (`(x IS NULL) OR (x > 0)`).

### Moved

| 0.1 | 0.2 |
|---|---|
| `sv.Pipeline`, `pipe.source`, `pipe.view`, `pipe.refresh` | transforms on sources, `node.write(sink)`, `node.refresh()`, `sv.group(...)` (`Pipeline` is internal: `sverify.incremental`) |
| `sv.IncrementalView(con, query, name)`, `view.apply`, `view.rows()` | a transform on a `StaticSource`, `source.apply(sv.Changes(...))`, `node.refresh()`, `node.to_arrow()` (`IncrementalView` is internal) |
| `pipe.view(..., resume=source.stored())` | build the nodes again; the first refresh resumes |
| `DeltaSink(uri, view).write()` | `node.write(DeltaSink(uri))`, written by `refresh` |
| `IcebergSink(catalog, identifier, view).write()` | `node.write(IcebergSink(catalog, identifier))` |
| `sverify.io.SinkWrite`, `sverify.io.IcebergWrite` | `sverify.io.SinkWrite` |
| `sv.StaticSource` | `sverify.io.StaticSource` |
| `sv.Changes` | `sv.Changes` (unchanged) |
| `sv.connect`, `sv.transform`, `sv.verify`, `sv.unique`, `sv.references`, `sv.Report`, `sv.asof_join` | unchanged |
| `sv.run_plan` | `sverify.engines.run` |
| `sv.run_substrait_json` | `sverify.engines.run_substrait_json` |
| `sv.create_table` | `sverify.engines.create_table` |
| `sv.table_rows` | `sverify.engines.table_rows` |
| `sv.ENGINES` | `sverify.engines.ENGINES` |
| `sv.SQL_PRODUCERS` | `sverify.engines.SQL_PRODUCERS` |
| `sv.Connection` | `sverify.engines.Connection` |
| `sv.substrait_json` | `sverify.engines.substrait_json` |
| `sv.isthmus_json` | `sverify.engines.isthmus_json` |
| `sv.written_plan` | `sverify.engines.written_plan` |
| `sv.delta_plans` | `sverify.engines.delta_plans` |
| `sverify.sql.to_sql`, `Dialect`, `Unsupported` | `sverify.engines.to_sql`, `Dialect`, `Unsupported` |
| `sverify.sql.duckdb.DUCKDB`, `sverify.sql.snowflake.SNOWFLAKE`, `sverify.sql.spark.SPARK` | `sverify.engines.DUCKDB`, `SNOWFLAKE`, `SPARK` |
| `sverify.partition.run_sharded` | `sverify.engines.run_sharded` |
| `sverify.spark_engine.run` | `sverify.engines.run_spark` |
| `sverify.spark_engine.SPARK_CONF` | `sverify.engines.SPARK_CONF` |
| `sv.VerificationError` | `sverify.errors.VerificationError` |
| `sv.PreconditionError` | `sverify.errors.PreconditionError` |
| `sv.PostconditionError` | `sverify.errors.PostconditionError` |
| `sv.CompositionError` | `sverify.errors.CompositionError` |
| `sv.NotIncremental` | `sverify.errors.NotIncremental` |
| `sv.SqlError` | `sverify.errors.SqlError` |
| `sverify.incremental.SchemaError` | `sverify.errors.SchemaError` |
| `sverify.incremental.AuditError` | `sverify.errors.AuditError` |
| `sv.Issue`, `sv.References`, `sv.Unique` | internal (`sverify.contracts`); `sv.unique` and `sv.references` build them |
| `sverify.io.ColumnStats`, `sverify.io.stats_facts`, `sverify.io.Stored` | internal (`sverify.io._common`, `sverify.incremental`) |
