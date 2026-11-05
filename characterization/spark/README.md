# Spark characterization

What open-source Spark does at each of the core's options
([core-semantics.md](../../docs/core-semantics.md)), recorded as facts, one
JSON document each in [facts/](facts/), in the format of
[fact.schema.json](../fact.schema.json) (`python -m sverify_dev.facts` checks
them). They are the evidence the Spark profile (#739) and its row of the
realizability table are built from. Databricks and Photon are out of scope.

Spark here is 4.3.0: the Python package `pyspark` 4.3.0, the version
`python/uv.lock` pins, and its sources at tag
[`v4.3.0`](https://github.com/apache/spark/tree/v4.3.0) (commit `98bc0212`).
The facts' `engine_version` is `4.3.0`. What is probed is Spark SQL, which
`sverify.spark_engine` writes plans to (`sverify.sql.spark`), on a local
session.

Each fact names the items of the characterization checklist
([../areas.json](../areas.json)) it settles; `python -m sverify_dev.facts
--coverage spark` lists them, and the rows of the engine choice tables each
fact settles. Every row and item is settled.

## How the facts are judged

As DuckDB's ([../duckdb/README.md](../duckdb/README.md#how-the-facts-are-judged)):
`Rel.eval` means Substrait's semantics, each function's extension YAML with
its options; where Substrait leaves a choice open, the reference raises if
engines disagree on an edge case, and otherwise takes the least surprising
value every backend can emulate; an engine's profile refines the loose core,
and its diff against the reference is its row of the realizability table
([Terminology](../../docs/core-semantics.md#terminology)). A fact's `status`
is `open` where Spark differs from the reference and the profile has not
decided how to bridge it, and `no-finding` where Spark gives the reference
natively under the settings it records.

Spark's behaviour turns on one setting above all: `spark.sql.ansi.enabled`,
on by default since 4.0 and in sverify's session (`SPARK_CONF` in
`sverify.sql.spark`). With it on, integer overflow, division by zero, bad
casts and indexes out of range raise, as the reference's defaults do. With
it off they wrap or give NULL. Every probe runs under both, and each fact
says what each gives; its `status` judges the ANSI behaviour, the one the
profile will target. The other settings that change results are in
[exec-settings](facts/spark-exec-settings.json).

## The probes

`python -m sverify_dev.probe_spark` (`python/tools/sverify_dev/probe_spark.py`)
writes [probes.json](probes.json): 273 SQL queries, each with its result.
Every query runs four times on one local session, with ANSI on and off, and
on each of Spark's two paths for a small query:

- folded: the optimizer evaluates a query over a `VALUES` table on the
  driver with the interpreted expressions (`ConvertToLocalRelation`,
  `ConstantFolding`), as it does for the small tables sverify hands Spark;
- codegen: those two rules are excluded, so the query runs as a job with
  whole-stage code generation, as it does over a real table.

Where the two paths agree, an entry keeps one result per ANSI setting
(`ansi=true`, `ansi=false`); where they differ, both
(`ansi=true folded`, `ansi=true codegen`). Facts cite the entries by their
`construct`. A JVM is too heavy for the test suite, so no test checks the
file is current; rerun it after a Spark upgrade, on homelab under
CLAUDE.md's rules:

```bash
cd python && uv run python -m sverify_dev.probe_spark --write
```

The probes ran on homelab: Linux x86-64, OpenJDK 21.0.12, `local[2]`,
session time zone UTC, `spark.sql.timestampType=TIMESTAMP_NTZ`. The order of
ties after a shuffle varies between runs (`sort-ties`), so a rerun can change
those entries. The trigonometric functions use `java.lang.Math` and a NaN
that arithmetic creates takes the CPU's sign, so their last bit and that sign
are the platform's ([exec-platform](facts/spark-exec-platform.json)).

Most facts also cite Spark's docs or its source at `v4.3.0`. Five findings are upstream bugs, SP-1 to SP-5 in
[upstream/bugs](../../upstream/bugs/), and one a spec gap,
[ST-16](../../upstream/bugs/ST-16.json).

## The Spark diff, as a table

How Spark 4.3.0 compares with the reference, option by option, under ANSI
mode; the ANSI-off behaviour follows in the same cell. "Native" means
Spark's own SQL gives the reference result.

| Function (types) | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `add` `subtract` `multiply` `negate` (`i8`…`i64`) | `overflow` | `ERROR` | native at every width; off: wraps | [int-arith](facts/spark-int-arith.json) |
| `abs` (`i8`…`i64`) | `overflow` | `ERROR` | native; off: `abs(MIN)` is `MIN` | [int-abs](facts/spark-int-abs.json) |
| `power` (integers) | `overflow`, negative exponent | `ERROR` | no integer power: a `DOUBLE` result, never raises | [int-pow](facts/spark-int-pow.json) |
| `divide` (`i8`…`i64`) | rounding | truncate | `div` truncates, but returns `BIGINT` at every width | [int-divide](facts/spark-int-divide.json) |
| | `on_division_by_zero` | `ERROR` | native; off: NULL | |
| | `overflow` (`MIN / -1`) | `ERROR` | native at `i64`; none below (a `BIGINT` result) | |
| `modulus` (`i8`…`i64`) | `division_type`, zero divisor, `MIN % -1` | `TRUNCATE`, `ERROR`, 0 | native; `pmod` floors; off: NULL for zero | [int-modulus](facts/spark-int-modulus.json) |
| `shift_left`, `shift_right` | range (ST-1) | drop bits, raise outside `[0, width)` | Java's shifts: count modulo 32 or 64, `i8`/`i16` promoted to `INT` | [int-shift](facts/spark-int-shift.json) |
| `sum` (`i8`…`i64`) | `overflow` | `ERROR` on the total | `BIGINT` result; raises on a 64-bit partial sum, by order and partitioning; off: wraps | [sum-int](facts/spark-sum-int.json) |
| `sum`, `avg` (all) | no values | NULL | native | sum-int, [sum-double](facts/spark-sum-double.json) |
| `avg` (integers) | `avg_int_result` | the declared type | `DOUBLE`, summed in double | [avg-int](facts/spark-avg-int.json) |
| decimals | result type, `decimal_rescale`, `overflow` | the YAML's, `TIE_AWAY_FROM_ZERO`, `ERROR` | native; off: NULL on overflow | [decimal-arith](facts/spark-decimal-arith.json) |
| `negate`, `abs` (decimals) | | exact | rounds past 34 digits, raises at 10³⁸ - 1 ([SP-1](../../upstream/bugs/SP-1.json)) | [decimal-negate](facts/spark-decimal-negate.json) |
| `add` `subtract` `multiply` (`fp32`, `fp64`) | `rounding` | `TIE_TO_EVEN` | native | [double-arith](facts/spark-double-arith.json) |
| | `nan_creation`, `float_overflow` | raise | NaN, `±inf`, in both modes | |
| `divide` (`fp32`, `fp64`) | `on_division_by_zero` | `ERROR` | native; off: NULL, never `±inf` | [double-divide](facts/spark-double-divide.json) |
| | `nan_creation` (`inf / inf`) | raise | NaN | |
| `modulus` (`fp64`) | | `fmod`, zero divisor raises | native but the zero's sign; off: NULL for zero | [double-modulus](facts/spark-double-modulus.json) |
| doubles | `zero_sign` | `ONE_ZERO` | two zeros in arithmetic; a `-0.0` literal is a decimal 0.0 | [zero-sign](facts/spark-zero-sign.json) |
| `sqrt`, `asin`, `acos`, `power`, trig of ±inf | `on_domain_error` | `ERROR` | NaN | [math-domain](facts/spark-math-domain.json) |
| `ln`, `log10`, `log2`, `logb` | `on_domain_error`, `on_log_zero` | `ERROR` | NULL for x ≤ 0 ([ST-16](../../upstream/bugs/ST-16.json)) | math-domain |
| `atan2` | `(0, 0)` (ST-2) | raise | 0; the zeros' signs dropped | math-domain |
| elementary functions | last bits | the platform's libm | `StrictMath` for exp, logs, `pow`; `Math` for the rest; `log2` two roundings | [elem-rounding](facts/spark-elem-rounding.json) |
| `round` | `rounding` | `TIE_AWAY_FROM_ZERO` | native | [round](facts/spark-round.json) |
| `round` to `d` digits | | on the binary value | on the shortest decimal text: `round(2.675, 2)` is 2.68 | round |
| `floor`, `ceil` (`fp64`) | | a double | `BIGINT`; ±inf raises, NaN is 0 ([SP-5](../../upstream/bugs/SP-5.json)) | round |
| `fp32` arithmetic | | refused (#417) | native single precision; aggregates and math functions widen | [fp32](facts/spark-fp32.json) |
| `sum`, `avg` (`fp64`) | `sum_order` | any order, within #85's bound | in arrival order per partition, merged by task | [sum-double](facts/spark-sum-double.json), [avg-double](facts/spark-avg-double.json) |
| `sum`, `avg`, `variance` over ±inf, NaN | `nan_creation`, `stat_degenerate` | raise | NaN, `±inf` | [nonfinite-aggregates](facts/spark-nonfinite-aggregates.json) |
| `variance`, `std_dev`, `covar_*`, `corr` | `stat_algo`, `stat_degenerate` | generic properties; NULL for degenerate cases | Welford, Chan merge; NULL for one value or pair (NaN under a legacy setting) | [var-stddev](facts/spark-var-stddev.json), [covar](facts/spark-covar.json), [corr](facts/spark-corr.json) |
| `quantile_cont`, `median` | `quantile_interp` | any double between neighbours | linear at (n - 1)·p | [quantile](facts/spark-quantile.json) |
| `quantile_disc` | | a value of the input's type | the value, as a `DOUBLE` | quantile |

### NULLs, NaN and order

| Function (types) | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `equal`, grouping, `DISTINCT`, joins (`fp64`) | `nan_equality` | `NAN_IS_NAN` | native; every NaN normalised in keys | [nan-equality](facts/spark-nan-equality.json) |
| `lt`, sorts, `max`, `greatest`, quantiles | `nan_order` | `GREATEST` | native | [nan-order](facts/spark-nan-order.json) |
| `equal`, sorts, grouping, `min`, `max` (`fp64`) | `zero_sign` | `ONE_ZERO` | equal; grouping normalises to 0.0; `min`, `max`, sorts keep the first zero | [zero-order](facts/spark-zero-order.json) |
| doubles | `nan_kind` | `ONE_NAN` | the sign survives `-x`; created NaN negative on x86-64 | [nan-sign](facts/spark-nan-sign.json) |
| sort key | `null_order` | as the key states | `NULLS FIRST` ascending, `NULLS LAST` descending by default; both honoured | [null-order](facts/spark-null-order.json) |
| sort, `fetch` | `tie_order` | any order | ties in partition order, varying between runs | [sort-stability](facts/spark-sort-stability.json) |
| sort key | `clustered` | equal keys adjacent | `CLUSTER BY` | [clustered](facts/spark-clustered.json) |
| `aggregate` keys, joins | NULL keys | one group; `=` skips NULL | native; `<=>`, `IS NOT DISTINCT FROM` | [null-keys](facts/spark-null-keys.json) |
| `and`, `or`, `not`, `bool_and`, `bool_or` | | Kleene; aggregates skip NULLs | native | [kleene](facts/spark-kleene.json) |
| `first`, `last`, `mode`, `arg_min`, `arg_max` | `tie_pick` | any row | arrival order; `mode` any of a tie | [first-last](facts/spark-first-last.json) |
| `string_agg`, `array_agg` | `tie_order` | any order | arrival order | first-last |
| `rank`, `ntile`, `percent_rank`, `cume_dist` | `ntile_spread`, `tie_order` | SQL's; NULLs ranked | native | [rank](facts/spark-rank.json) |
| `lag`, `first_value`, windowed sums | frame, `tie_order` | the window's | SQL's default frame, native | [window-values](facts/spark-window-values.json) |
| `UNION`, `INTERSECT`, `EXCEPT` | | NULLs equal | native, `ALL` forms too | [set-operations](facts/spark-set-operations.json) |

### Strings, dates, casts and lists

| Function (types) | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `upper`, `lower` | `char_set` | `UTF8`, full mappings | native, in the JVM's default locale | [case](facts/spark-case.json) |
| `like`, `starts_with`, `strpos`, `replace` | `case_sensitivity` | `CASE_SENSITIVE` | native | [match-functions](facts/spark-match-functions.json) |
| `substring` | `negative_start` | `WRAP_FROM_END`, 1-based | native but a start of 0, which reads as 1 | [substring](facts/spark-substring.json) |
| | `substring_range` | raise outside `[-2³², 2³²)` | `INT` positions: raise from 2³¹ on; off: wrap | [substring-range](facts/spark-substring-range.json) |
| `strpos` | `string_positions` | 1-based characters, 0 when absent | native (`instr`) | [strpos](facts/spark-strpos.json) |
| `character_length`, `reverse`, `btrim` | | code points; spaces | native | [string-plain](facts/spark-string-plain.json) |
| `str_concat` | `null_handling` | `ACCEPT_NULLS` | native; `concat_ws` skips NULLs | [concat](facts/spark-concat.json) |
| `regexp_extract`, `regexp_replace` | `regex_dialect` | RE2; `''` without a match | `java.util.regex`, ASCII classes, `$1`; `''` without a match | [regex](facts/spark-regex.json) |
| `md5`, `sha256` | `digests` | hex of the UTF-8 bytes | native (`sha2(s, 256)`) | [digests](facts/spark-digests.json) |
| date and timestamp arithmetic | `date_range` | raise outside 0001 … 9999 | computes past them; `date_add` wraps at 2³¹ days ([SP-2](../../upstream/bugs/SP-2.json)); a bare `long overflow` at the end of the timestamp range ([SP-3](../../upstream/bugs/SP-3.json)) | [date-range](facts/spark-date-range.json) |
| `TIME ± INTERVAL` | `time_interval_months` | refused | `TIME` off by default; with it, raises past midnight | [time-type](facts/spark-time-type.json) |
| timestamps | precision | microseconds | native | [timestamp-precision](facts/spark-timestamp-precision.json) |
| time zones | | outside the model | session zone; gaps forward, overlaps earlier | [time-zones](facts/spark-time-zones.json) |
| `date_part`, `date_trunc` | `week_numbering` | ISO weeks, floor before 1970 | native; `dayofweek` counts from Sunday | [week-parts](facts/spark-week-parts.json) |
| `cast` `fp64` → integer | `float_to_int`, `cast_failure` | `TRUNCATE`, raise | native; off: saturate (`INT`, `BIGINT`) or wrap | [cast-double-to-int](facts/spark-cast-double-to-int.json) |
| `cast` from and to strings | parsing, formatting | the reference's rules | lenient parsing (trims, hex floats, `1.5d`); Java's double text | [cast-string](facts/spark-cast-string.json) |
| `cast` with `RETURN_NULL` | `try_variants` | NULL on failure | `try_cast`, and `try_*` for arithmetic | [try-variants](facts/spark-try-variants.json) |
| `<` and sorts of lists | `list_null_order` | NULL in `<`, `GREATEST` in sorts | a NULL element lowest in both | [list-order](facts/spark-list-order.json) |
| `list_extract` | indexing | 1-based | `element_at` 1-based, 0 raises; `[]` 0-based | [list-index](facts/spark-list-index.json) |
| `=` on structs and lists | | structural, NULLs equal | native | [nested-equality](facts/spark-nested-equality.json) |
| `UNNEST` | NULL and empty lists | no row | native (`explode`) | [explode](facts/spark-explode.json) |

### Execution, frontend and I/O

| Construct | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `CASE`, `AND`, filters | `evaluation_order` | a branch sees only its rows | `CASE`, `IF`, `COALESCE` lazy; `AND`, `OR` short-circuit left to right; pushdown only removes raises | [exec-evaluation-order](facts/spark-exec-evaluation-order.json) |
| extra raises | `raise_set` | D2 | `INT` positions, ANSI string coercion, `element_at(…, 0)`, regexes, week patterns; two errors without a class | [raise-set](facts/spark-raise-set.json) |
| settings | | none | ANSI, timestamp type, time zone, legacy statistics, decimal precision loss, `TIME`, the JVM locale | [exec-settings](facts/spark-exec-settings.json) |
| parallelism | | bags; open orders | double sums, `BIGINT` sum overflow, `first`, ties vary with partitioning | [exec-parallel](facts/spark-exec-parallel.json) |
| platform | | black-box libm, one NaN | `Math` intrinsics, NaN sign, locale | [exec-platform](facts/spark-exec-platform.json) |
| sizes | | decimals to 38 digits | decimals to 38; strings and arrays below 2³¹ | [exec-size-limits](facts/spark-exec-size-limits.json) |
| streaming | | none | batch only | [exec-streaming-fallback](facts/spark-exec-streaming-fallback.json) |
| types | names, implicit casts, literals | explicit in the plan | Spark's names; ANSI precedence; `INT` literals, `1.5` a decimal | [type-names](facts/spark-type-names.json), [implicit-casts](facts/spark-implicit-casts.json), [literal-types](facts/spark-literal-types.json) |
| I/O | formats, object stores, catalogs | outside the plan | Parquet, ORC, CSV, JSON, Avro; Hadoop connectors; catalog plugins | [io](facts/spark-io.json) |
