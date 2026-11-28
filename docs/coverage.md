# Ibis coverage

How much of the Ibis API gets through to the checker, and which engines run
the plans of what verifies. The table comes from
[`sverify_dev/coverage.py`](../python/tools/sverify_dev/coverage.py) and its cases in
[`sverify_dev/coverage_cases/`](../python/tools/sverify_dev/coverage_cases), and the
`Generated files` workflow rewrites it on `main` after every merge
(`uv run python -m sverify_dev.coverage --write`). The 1.0 targets for SQL, Ibis and
dbt are in [coverage-targets.md](coverage-targets.md).

<!-- coverage:start -->
201 of 221 probed Ibis operations reach the checker (✓ verified, ✗ rejected by the checker, – fails in Ibis; *inc.* marks incremental maintenance).

| Area | Operations |
|---|---|
| rows | ✓ filter, select *inc.* · ✓ mutate *inc.* · ✓ drop, rename *inc.* · ✓ drop_null *inc.* · ✓ isnull *inc.* · ✓ between *inc.* · ✓ isin *inc.* · ✓ notin *inc.* · ✓ ifelse *inc.* · ✓ cases *inc.* · ✓ order_by *inc.* · ✓ limit · ✓ limit with offset · ✓ order_by + limit · ✗ sample · ✓ order_by expression *inc.* · ✗ limit expression · ✗ limit count() · ✓ fill_null table *inc.* · ✓ fill_null all *inc.* · ✓ memtable *inc.* · ✓ constant table *inc.* · ✓ alias *inc.* · ✓ sql view *inc.* · ✓ sql query *inc.* |
| joins | ✓ inner join *inc.* · ✓ non-equi join *inc.* · ✓ cross join *inc.* · ✓ left join · ✓ right join · ✓ outer join · ✓ semi join · ✓ anti join · ✓ isin subquery · ✓ isin subquery in select · ✓ notin subquery · ✓ scalar subquery in select · ✓ scalar subquery, one row · ✗ scalar subquery, many rows · ✓ exists · ✓ not exists · ✓ exists, uncorrelated · ✗ correlated scalar subquery · ✓ union all *inc.* · ✓ union distinct · ✓ intersect · ✓ difference · ✓ intersect all · ✓ difference all |
| aggregation | ✓ count() · ✓ group_by sum · ✓ count, max, mean · ✓ arithmetic over aggregates · ✓ nunique · ✓ first, last ordered · ✓ group_concat ordered · ✓ group_concat · ✗ approx_nunique · ✓ any, all · ✓ bit_and, bit_or, bit_xor · ✓ sum(where=) · ✓ having · ✓ value_counts · ✓ distinct · ✓ distinct(on=) · ✓ std · ✓ cov, corr · ✓ collect · ✓ collect ordered · ✗ collect include_null · ✓ scalar subquery · ✓ unnest · ✓ median, quantile · ✓ mode · ✓ mode of an expression · ✓ arbitrary · ✓ nunique of rows · ✓ argmin, argmax · ✗ approx_median · ✓ quantile of several |
| lists | ✓ unnest column · ✓ unnest keep_empty · ✓ list literal *inc.* · ✓ list column *inc.* · ✓ pivot_longer *inc.* |
| windows | ✓ row_number · ✓ lag · ✓ rank · ✓ dense_rank · ✓ cumsum · ✓ sum over group · ✓ rolling mean (rows) · ✓ rolling mean (interval) · ✓ ntile · ✓ first · ✓ percent_rank, cume_dist · ✓ running mean · ✓ rolling sum (interval) · ✓ rolling sum (range) · ✓ last, nth · ✓ max, count over frame · ✓ min over a sliding frame · ✓ window sum of an expression · ✓ window over expressions · ✓ group_concat over a window · ✓ stddev over group · ✓ rolling variance (rows) |
| numbers | ✓ +, -, * *inc.* · ✓ float division *inc.* · ✓ integer division *inc.* · ✓ mod *inc.* · ✓ decimal mod *inc.* · ✓ abs *inc.* · ✓ round *inc.* · ✓ ceil, floor *inc.* · ✓ power *inc.* · ✓ greatest *inc.* · ✓ least *inc.* · ✓ clip *inc.* · ✓ cast int → double *inc.* · ✓ cast int → string *inc.* · ✓ cast boolean → string *inc.* · ✓ cast date → string *inc.* · ✓ cast double → int *inc.* |
| math | ✓ sign *inc.* · ✓ sqrt *inc.* · ✓ exp *inc.* · ✓ ln *inc.* · ✓ log10, log2 *inc.* · ✓ log(base) *inc.* · ✓ trigonometry *inc.* · ✓ atan2 *inc.* · ✓ degrees, radians *inc.* · ✓ pi, e *inc.* · ✓ isinf *inc.* · ✓ bitwise *inc.* · ✓ shifts *inc.* · ✓ logical xor *inc.* |
| nulls | ✓ fill_null *inc.* · ✓ coalesce *inc.* · ✓ nullif *inc.* |
| strings | ✓ upper *inc.* · ✓ length *inc.* · ✓ concat *inc.* · ✓ substr *inc.* · ✓ contains *inc.* · ✓ startswith *inc.* · ✓ like *inc.* · ✓ re_search *inc.* · ✓ strip *inc.* · ✓ lpad *inc.* · ✓ rpad *inc.* · ✓ repeat *inc.* · ✓ reverse *inc.* · ✓ right *inc.* · ✓ replace *inc.* · ✓ replace '' *inc.* · ✓ ilike *inc.* · ✓ find from *inc.* · ✓ ascii *inc.* · ✓ join *inc.* · ✓ levenshtein *inc.* · ✓ find_in_set *inc.* · ✓ capitalize *inc.* · ✓ slice *inc.* · ✗ translate · ✓ re_extract *inc.* · ✓ re_replace *inc.* · ✓ hexdigest *inc.* · ✗ hash · ✗ host |
| time | ✓ timestamp + interval *inc.* · ✓ compare with literal *inc.* · ✓ year *inc.* · ✓ date *inc.* · ✓ truncate *inc.* · ✓ date + days *inc.* · ✓ date - months *inc.* · ✓ date + years *inc.* · ✓ date - column days *inc.* · ✓ timestamp + months *inc.* · ✓ constant interval arithmetic *inc.* · ✓ date - date *inc.* · ✓ date delta *inc.* · ✓ date parts *inc.* · ✓ date truncate *inc.* · ✓ day_of_week *inc.* · ✓ day_of_week name *inc.* · ✓ iso_year *inc.* · ✓ epoch_seconds *inc.* · ✓ millisecond, microsecond *inc.* · ✓ timestamp + column interval *inc.* · ✓ date + column months *inc.* · ✓ timestamp delta *inc.* · ✓ bucket *inc.* · ✓ group_by_dynamic (no overlap) · ✓ rolling sum by time · ✓ offset_by months and days *inc.* · ✓ month end *inc.* · ✗ group_by_dynamic (overlapping) · ✓ time of day *inc.* · ✓ time parts *inc.* · ✓ compare times *inc.* · ✓ strftime *inc.* · ✓ timestamp from unix *inc.* · ✓ date from constants *inc.* · ✓ timestamp from constants *inc.* · ✓ date from columns *inc.* · ✗ string to timestamp · ✓ time + interval *inc.* · ✓ time truncate *inc.* · ✗ strftime other directives · – between_time |
| generic | ✓ try_cast *inc.* · ✓ try_cast string *inc.* · ✗ param · ✓ typeof *inc.* · ✗ random · ✗ uuid · ✗ now · ✗ today |

Every engine runs the plans of the 201 verified operations, except:

| Engine | Runs | Refuses |
|---|---|---|
| DuckDB | 201 | — |
| Polars | 174 | first, last ordered · group_concat ordered · group_concat · distinct(on=) · cov, corr · median, quantile · mode · mode of an expression · arbitrary · argmin, argmax · quantile of several · group_concat over a window · stddev over group · rolling variance (rows) · cast date → string · levenshtein · re_extract · re_replace · hexdigest · timestamp + column interval · date + column months · timestamp delta · date from columns · time + interval · time truncate · try_cast · try_cast string |
| Snowflake | 157 | non-equi join · first, last ordered · group_concat ordered · group_concat · distinct(on=) · cov, corr · collect · collect ordered · unnest · median, quantile · mode · mode of an expression · arbitrary · argmin, argmax · quantile of several · unnest column · unnest keep_empty · list literal · group_concat over a window · stddev over group · rolling variance (rows) · decimal mod · cast date → string · sqrt · exp · ln · log10, log2 · log(base) · trigonometry · atan2 · shifts · upper · capitalize · re_extract · re_replace · hexdigest · timestamp + column interval · date + column months · timestamp delta · date from columns · time + interval · time truncate · try_cast · try_cast string |
| Spark | 171 | non-equi join · first, last ordered · group_concat ordered · group_concat · distinct(on=) · cov, corr · collect ordered · median, quantile · mode · mode of an expression · arbitrary · argmin, argmax · quantile of several · group_concat over a window · cast date → string · atan2 · re_extract · re_replace · hexdigest · timestamp + column interval · date + column months · timestamp delta · time of day · time parts · compare times · date from columns · time + interval · time truncate · try_cast · try_cast string |
<!-- coverage:end -->

The engines refuse what they can't do as Lean does: `<` on strings is
undefined in the model (it is NULL there, while SQL compares), and Snowflake
and Spark tables have no row order, so `to_sql` writes FETCH and windows with
ties and a `LIMIT`'s rows open, as the reference allows, and refuses
`rows="sequence"` for them. A `SUM` or `AVG` of doubles runs natively on every engine, within the
plan's bound of the reference's correctly rounded sum
([float-bounds.md](float-bounds.md)). See
[Engines and SQL](how-to-engines-and-sql.md#engines-and-sql).
