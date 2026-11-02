# Upstream bugs ledger

Bugs and surprising behaviours that sverify found in the projects it builds
on: SQLGlot, the engines (DuckDB, Polars, DataFusion, Spark), Ibis and
Substrait's tooling. **We file them upstream in batches**, so each entry
records enough to file it: the version, a minimal reproduction, and how
sverify works around it today.

Add an entry whenever you find one, in the same PR as the workaround.
Engine behaviour that is *documented and intended*, and differs from the
reference model, isn't a bug: it belongs in that engine's characterization
(`characterization/<engine>/FACTS.md`) and profile, not here.

**Status:** `unverified` (seen, not yet reduced to a minimal repro or
checked against the latest upstream release), `confirmed` (minimal repro on
the stated version), `filed <link>`, `fixed upstream in <version>`, or
`not a bug` (with the reason).

## SQLGlot

| ID | Version | Status | Summary | Minimal repro | Our handling | Found by |
|---|---|---|---|---|---|---|
| SG-1 | 30.27.0 | confirmed | `qualify` resolves a name in `WHERE`/`GROUP BY`/`HAVING` that is both an input column and an output alias as the **alias**; DuckDB resolves it as the **column**. | `select a + 1 as a from t group by a having a = 42` with `t(a) = [42]`: DuckDB returns 43, the qualified tree returns nothing. | The lift refuses such names (#252, b387dcd). | sqllogictest replay through the lift (#252) |
| SG-2 | 30.27.0 | unverified | Transpiling between dialects keeps the text of an operator whose meaning differs: `transpile("select 7/2", read="postgres", write="duckdb")` gives `SELECT 7 / 2` (3 in Postgres, 3.5 in DuckDB). With a schema plus `annotate_types`, it becomes `CAST(TRUNC(a / b) AS BIGINT)` (right value, BIGINT where Postgres gives INTEGER). | as stated | sverify never uses SQLGlot's transpiler for semantics (#231); the lift's profiles decide. May be a known limitation upstream, not a bug: check their docs and issues first. | #231 findings |
| SG-3 | 30.27.0 | unverified | DuckDB → DataFusion transpiling rewrites some functions with another meaning: `strftime`, top-n `min(x, n)`, `POSITIONAL`/`ASOF` joins, `TRY`. | see `tools/sverify_dev/slt.py`'s refusal list | Obsolete for sverify: the replay no longer transpiles (#264). File only if still present upstream. | sqllogictest replay (#201) |
| SG-4 | 30.22.0 | confirmed | The tokenizer reads every underscore in a number as a digit separator. DuckDB reads only an underscore between two digits so; anywhere else it starts an alias. | `SELECT 1__2` is 1 (named `__2`) in DuckDB, 12 in SQLGlot; `SELECT 1._5` is 1 (named `_5`), 1.5 in SQLGlot. `1_000` agrees. | The lift refuses a number with an underscore not between two digits (`_check_numbers`). | sqllogictest replay through the lift, `parser/digit_separators.test`, `parser/unquoted_underscore_digit_identifiers.test` |
| SG-5 | 30.22.0 | confirmed | `qualify` expands `t.*` of the right table of a `JOIN … USING` without the `USING` columns; DuckDB keeps them in `t.*` (only `*` shows them once). | `SELECT a.*, b.* FROM a JOIN b USING (i)`: DuckDB gives 4 columns, the qualified tree 3. | The lift refuses `t.*` with `USING` (`_check_using_stars`). | replay, `join/empty_joins.test` |

## DataFusion 51 (Substrait producer and SQL planner)

DataFusion is now a backend only (#211). Producer and planner bugs no longer
affect sverify's results, but they're worth reporting.

| ID | Status | Summary | Minimal repro | Our handling | Found by |
|---|---|---|---|---|---|
| DF-1 | confirmed | `EXCEPT ALL` is planned as a left anti join, which loses multiplicities. | `[1,1,2,3] EXCEPT ALL [1,3]` gives `[2]`, not `[1,2]` (DuckDB `setops/test_pg_union.test:339,350`) | Frontend no longer used (#264) | replay, FACTS S6 |
| DF-2 | confirmed | `FETCH FIRST n ROWS ONLY` is dropped: the plan has no limit. | DuckDB `parser/fetch_first.test` | as above | FACTS S6 |
| DF-3 | confirmed | The Substrait producer drops `DISTINCT` and `FILTER (WHERE …)` of a window aggregate: `COUNT(DISTINCT s) OVER (…)` counts every row. | DuckDB `window/test_window_distinct.test:76` | as above | FACTS S6 |
| DF-4 | unverified | `GROUP BY k, k` writes two grouping expressions, and the projection above reads the aggregate's columns shifted by one. Could also be sverify's reading of a repeated grouping expression: check first. | DuckDB `aggregate/group/test_group_by.test:149` | — | FACTS S6 |
| DF-5 | confirmed | `SELECT *` of a `NATURAL JOIN` keeps both copies of the join columns. | DuckDB `catalog/case_insensitive_using.test:123-138` | as above | FACTS S6 |
| DF-6 | confirmed | The Substrait producer writes `FROM (VALUES …)` as an empty virtual table: the rows are dropped. | any `SELECT * FROM (VALUES (1), (2))` | as above | FACTS S3 |
| DF-7 | unverified | SQL decimal literals beyond double precision are read as doubles: `100000000000000000000 > 99999999999999999999.99999` is false. Possibly intended. | DuckDB `cast/decimal_float_cast.test:10` | — | FACTS S4 |
| DF-8 | unverified | The Substrait producer encodes grouping sets against the spec: the extra column is a bitmask where the spec says the grouping set's index, and the grouping expressions are laid out differently. | TPC-DS q27/q36 (#229) | Grouping sets come through the SQLGlot lift instead (M2) | pi3, #229 |
| DF-9 | confirmed | The Substrait producer registers no proper extension URNs (placeholder references). | any plan with a function | Not needed anymore | #231 findings |
| DF-10 | unverified | The Substrait consumer doesn't know Substrait's `shift_left`/`shift_right`. | a plan calling them, run through `from_substrait_plan` | DataFusion refuses those plans | #215 |
| DF-11 | confirmed | `NTILE(k)` computes `⌊i · min(k, n) / n⌋ + 1`, which spreads the larger buckets out; the SQL standard (and DuckDB, Spark, Snowflake, PostgreSQL) puts the `n % k` larger buckets first. | `select ntile(4) over (order by i) from (values (0),(1),(2),(3),(4),(5),(6),(7),(8),(9)) t(i)` gives `1 1 1 2 2 3 3 3 4 4`; the standard gives `1 1 1 2 2 2 3 3 4 4` (DataFusion 51.0.0) | Lean's `ntileOf` is the standard's; `datafusion_plan` refuses NTILE | M2 (ntile) |

## DuckDB 2.0

| ID | Status | Summary | Minimal repro | Our handling | Found by |
|---|---|---|---|---|---|
| DD-1 | unverified | `levenshtein` counts bytes, not code points, on non-ASCII text, and `reverse` works on grapheme clusters. Possibly intended: check the docs before filing. | `levenshtein('é', 'e')` | sverify raises "non-ASCII text differs between engines" for these on DuckDB (#195) | #195 |
| DD-2 | not a bug (probably) | `error()` with a message built by `concat` shows a NULL argument as an empty string. That's `concat`'s documented NULL handling. | `error(concat('x: ', NULL))` | Guards keep NULL out of the error branch (#255) | #255 |
| DD-3 | confirmed | `VAR_POP` and `STDDEV_POP` of a single NaN are `0.0`, not NaN; with a second value they are NaN. IEEE and every other engine propagate the NaN. | `select var_pop(x) from (values ('nan'::double)) t(x)` gives `0.0` | The SQL writer returns NaN when an input is NaN (#54) | #54 |
| DD-4 | confirmed | `read_parquet` trusts a file's min/max statistics for doubles, which Parquet writers compute without NaN. Comparisons are folded from them and row groups skipped, though DuckDB orders NaN above every double: NaN rows go missing or compare wrongly. | A Parquet file of `x = [0.5, NaN]` written by pyarrow 26 (min = max = 0.5): `select x <= 100.0 from read_parquet(f)` is TRUE for the NaN, `... where x > 100.0` counts 0 rows, `select max(x)` gives 0.5. | A `Scan` reads each double column through `CASE WHEN isnan(x) THEN 'NaN' ELSE x + 0.0 END`, which DuckDB keeps no statistics for (#173) | #173 |

## Polars, Spark, Ibis

Nothing yet.
