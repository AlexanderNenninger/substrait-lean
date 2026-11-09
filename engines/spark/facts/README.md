# Spark characterization

What open-source Spark does at each of the core's options
([core-semantics.md](../../../docs/core-semantics.md)), recorded as facts, one
JSON document each in [facts/](./), in the format of
[fact.schema.json](../../../characterization/fact.schema.json) (`python -m sverify_dev.facts` checks
them). They are the evidence `Profile.spark`
(`SubstraitLean/SparkProfile.lean`, the profile `verify(semantics="spark")`
checks under; [Spark as a
profile](../../../docs/engine-profiles.md#spark-as-a-profile), #739) and its row
of the realizability table are built from. Databricks and Photon are out of scope.

Spark here is 4.3.0: the Python package `pyspark` 4.3.0, the version
`python/uv.lock` pins, and its sources at tag
[`v4.3.0`](https://github.com/apache/spark/tree/v4.3.0) (commit `98bc0212`).
The facts' `engine_version` is `4.3.0`. What is probed is Spark SQL, which
`sverify_spark.engine` writes plans to (`sverify_spark.dialect`), on a local
session.

Each fact names the items of the characterization checklist
([areas.json](../../../characterization/areas.json)) it settles; `python -m sverify_dev.facts
--coverage spark` lists them, and the rows of the engine choice tables each
fact settles. Every row and item is settled.

## How the facts are judged

The facts are judged as every engine's are
([../README.md](../../../characterization/README.md#how-the-facts-are-judged)). A fact's `status` is `open` where Spark differs from the reference and
the profile has not decided how to bridge it, and `no-finding` where Spark
gives the reference natively under the settings it records.

Spark's behaviour turns on one setting above all: `spark.sql.ansi.enabled`,
on by default since 4.0 and in sverify's session (`SPARK_CONF` in
`sverify_spark.dialect`). With it on, integer overflow, division by zero, bad
casts and indexes out of range raise, as the reference's defaults do. With
it off they wrap or give NULL. Every probe runs under both, and each fact
says what each gives; its `status` judges the ANSI behaviour, the one the
profile targets. The other settings that change results are in
[exec-settings](spark-exec-settings.json).

## The probes

`python -m sverify_dev.probe_spark` (`python/tools/sverify_dev/probe_spark.py`)
writes [probes.json](../probes/probes.json): 273 SQL queries, each with its result.
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
are the platform's ([exec-platform](spark-exec-platform.json)).

Most facts also cite Spark's docs or its source at `v4.3.0`. Seven findings are upstream bugs, SP-1 to SP-7 in
[upstream/bugs](../../../upstream/bugs/), and one a spec gap,
[ST-16](../../../upstream/bugs/ST-16.json).

## Spark's tests

Spark ships its SQL tests with their expected output at each release tag:
the queries in `sql/core/src/test/resources/sql-tests/inputs/` and the golden
files `results/*.sql.out` that `SQLQueryTestSuite` checks. Those under
`results/` run with ANSI on, those under `results/nonansi/` with it off, in
the time zone America/Los_Angeles. A fact's `engine-test` check links each
case that pins its behaviour at `v4.3.0`, from its `-- !query` line to its
last line of output, with a note on what it shows.

`python -m sverify_dev.spark_tests` (`python/tools/sverify_dev/spark_tests.py`)
clones the tests at the tag into `~/.cache/sverify/spark-tests` (a sparse
clone, about 20 MB) and searches them; `check` checks that every link names a
case of a golden file at the tag, and `replay` runs a golden file on the
local `pyspark` and compares the output (it needs a JVM):

```bash
cd python
uv run python -m sverify_dev.spark_tests search 'try_add\(' --file nonansi
uv run python -m sverify_dev.spark_tests check
```

A replay against `Rel.eval`, as `sverify_dev.slt` does for DuckDB's
sqllogictests, would need a lift of Spark's SQL, which sverify does not have.
The golden files run each query once and sort the rows of a query without an
`ORDER BY`, so they cannot show what varies between runs or partitionings
(ties, the order of a sum); the [evidence table](#evidence-fact-by-fact) gives
the reason for each fact with no case.

Reading the tests corrected four facts: `FLOAT / FLOAT` is a `DOUBLE`
([fp32](spark-fp32.json)); under ANSI a string next to a `FLOAT`,
`DOUBLE` or decimal is read as `DOUBLE`
([implicit-casts](spark-implicit-casts.json));
`try_element_at(a, 0)` raises like `element_at`
([try-variants](spark-try-variants.json),
[list-index](spark-list-index.json)); and XML is a built-in source
([io](spark-io.json)).

## Fuzzing the open deviations

`python -m sverify_dev.spark_fuzz` (`python/tools/sverify_dev/spark_fuzz.py`)
runs each open deviation's constructs on random rows that lean on the edges
the fact names (bounds, zeros, NaN, ±inf, NULL, long decimals), under ANSI on
and off, on both paths, and compares each result (its value, its type, or its
error class) with a model of what the fact says. Aggregates run over many
groups with `spark.sql.leafNodeDefaultParallelism` at 1, 2 and 3: Spark scans
a local table in slices of consecutive rows, and the models of the sums,
`avg`, the variances and the covariances follow the fact's algorithm slice by
slice, then merge the partial results in any order. Where the construct has
a DuckDB form, `Rel.eval` (the reference profile of sverify's lift) runs on
the same rows, and the run counts the rows where Spark's value differs from
it. The run writes [fuzz.json](../probes/fuzz.json): per target, the seed, the rows,
the settings, the counts and any findings. It ran on homelab:

```bash
cd python && uv run python -m sverify_dev.spark_fuzz --rows 300 --seed 738
```

The run of 2026-11-05 (Spark 4.3.0, Java 21.0.12, Linux x86-64) checked
145,610 results over 44 targets, which cover the 36 open deviations, and
every one came out as its fact says. `--dry` runs the models alone, without
Spark. The fuzzing corrected four facts first:

- `-x` of a decimal past 34 digits rounds half to even (`DECIMAL128`), and
  `abs` rounds only a negative value
  ([decimal-negate](spark-decimal-negate.json),
  [SP-1](../../../upstream/bugs/SP-1.json)); `0 - x` keeps the scale only up to
  6, so the workaround SP-1 proposes loses a digit past it;
- `pmod` on doubles adds the divisor only to a negative remainder
  ([double-modulus](spark-double-modulus.json));
- `power(±1, ±inf)` and `power(1, NaN)` are NaN, `StrictMath.pow`'s rule
  ([math-domain](spark-math-domain.json));
- decimal text with more than 38 integer digits raises
  `NUMERIC_OUT_OF_SUPPORTED_RANGE` ([exec-size-limits](spark-exec-size-limits.json)).

A fact's `fuzz` check names its targets in [fuzz.json](../probes/fuzz.json). Where a
target covers only some of a row's types (`DOUBLE` and not `FLOAT`, `BIGINT`
and not the narrower integers), the row keeps `probe` for the others.

## The Spark diff, as a table

How Spark 4.3.0 compares with the reference, option by option, under ANSI
mode; the ANSI-off behaviour follows in the same cell. "Native" means
Spark's own SQL gives the reference result.

| Function (types) | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `add` `subtract` `multiply` `negate` (`i8`…`i64`) | `overflow` | `ERROR` | native at every width; off: wraps | [int-arith](spark-int-arith.json) |
| `abs` (`i8`…`i64`) | `overflow` | `ERROR` | native; off: `abs(MIN)` is `MIN` | [int-abs](spark-int-abs.json) |
| `power` (integers) | `overflow`, negative exponent | `ERROR` | no integer power: a `DOUBLE` result, never raises | [int-pow](spark-int-pow.json) |
| `divide` (`i8`…`i64`) | rounding | truncate | `div` truncates, but returns `BIGINT` at every width | [int-divide](spark-int-divide.json) |
| | `on_division_by_zero` | `ERROR` | native; off: NULL | |
| | `overflow` (`MIN / -1`) | `ERROR` | native at `i64`; none below (a `BIGINT` result) | |
| `modulus` (`i8`…`i64`) | `division_type`, zero divisor, `MIN % -1` | `TRUNCATE`, `ERROR`, 0 | native; `pmod` floors; off: NULL for zero | [int-modulus](spark-int-modulus.json) |
| `shift_left`, `shift_right` | range (ST-1) | drop bits, raise outside `[0, width)` | Java's shifts: count modulo 32 or 64, `i8`/`i16` promoted to `INT` | [int-shift](spark-int-shift.json) |
| `sum` (`i8`…`i64`) | `overflow` | `ERROR` on the total | `BIGINT` result; raises on a 64-bit partial sum, by order and partitioning; off: wraps | [sum-int](spark-sum-int.json) |
| `sum`, `avg` (all) | no values | NULL | native | sum-int, [sum-double](spark-sum-double.json) |
| `avg` (integers) | `avg_int_result` | the declared type | `DOUBLE`, summed in double | [avg-int](spark-avg-int.json) |
| decimals | result type, `decimal_rescale`, `overflow` | the YAML's, `TIE_AWAY_FROM_ZERO`, `ERROR` | native; off: NULL on overflow | [decimal-arith](spark-decimal-arith.json) |
| `negate`, `abs` (decimals) | | exact | rounds past 34 digits half to even, raises at 10³⁸ - 1 ([SP-1](../../../upstream/bugs/SP-1.json)) | [decimal-negate](spark-decimal-negate.json) |
| `add` `subtract` `multiply` (`fp32`, `fp64`) | `rounding` | `TIE_TO_EVEN` | native | [double-arith](spark-double-arith.json) |
| | `nan_creation`, `float_overflow` | raise | NaN, `±inf`, in both modes | |
| `divide` (`fp32`, `fp64`) | `on_division_by_zero` | `ERROR` | native; off: NULL, never `±inf` | [double-divide](spark-double-divide.json) |
| | `nan_creation` (`inf / inf`) | raise | NaN | |
| `modulus` (`fp64`) | | `fmod`, zero divisor raises | native but the zero's sign; off: NULL for zero | [double-modulus](spark-double-modulus.json) |
| doubles | `zero_sign` | `ONE_ZERO` | two zeros in arithmetic; a `-0.0` literal is a decimal 0.0 | [zero-sign](spark-zero-sign.json) |
| `sqrt`, `asin`, `acos`, `power`, trig of ±inf | `on_domain_error` | `ERROR` | NaN | [math-domain](spark-math-domain.json) |
| `ln`, `log10`, `log2`, `logb` | `on_domain_error`, `on_log_zero` | `ERROR` | NULL for x ≤ 0 ([ST-16](../../../upstream/bugs/ST-16.json)) | math-domain |
| `atan2` | `(0, 0)` (ST-2) | raise | 0; the zeros' signs dropped | math-domain |
| elementary functions | last bits | the platform's libm | `StrictMath` for exp, logs, `pow`; `Math` for the rest; `log2` two roundings | [elem-rounding](spark-elem-rounding.json) |
| `round` | `rounding` | `TIE_AWAY_FROM_ZERO` | native | [round](spark-round.json) |
| `round` to `d` digits | | on the binary value | on the shortest decimal text: `round(2.675, 2)` is 2.68 | round |
| `floor`, `ceil` (`fp64`) | | a double | `BIGINT`; ±inf raises, NaN is 0 ([SP-5](../../../upstream/bugs/SP-5.json)) | round |
| `fp32` arithmetic | | refused (#417) | native single precision; aggregates and math functions widen | [fp32](spark-fp32.json) |
| `sum`, `avg` (`fp64`) | `sum_order` | any order, within #85's bound | in arrival order per partition, merged by task | [sum-double](spark-sum-double.json), [avg-double](spark-avg-double.json) |
| `sum`, `avg`, `variance` over ±inf, NaN | `nan_creation`, `stat_degenerate` | raise | NaN, `±inf` | [nonfinite-aggregates](spark-nonfinite-aggregates.json) |
| `variance`, `std_dev`, `covar_*`, `corr` | `stat_algo`, `stat_degenerate` | generic properties; NULL for degenerate cases | Welford, Chan merge; NULL for one value or pair (NaN under a legacy setting) | [var-stddev](spark-var-stddev.json), [covar](spark-covar.json), [corr](spark-corr.json) |
| `quantile_cont`, `median` | `quantile_interp` | any double between neighbours | linear at (n - 1)·p | [quantile](spark-quantile.json) |
| `quantile_disc` | | a value of the input's type | the value, as a `DOUBLE` | quantile |

### NULLs, NaN and order

| Function (types) | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `equal`, grouping, `DISTINCT`, joins (`fp64`) | `nan_equality` | `NAN_IS_NAN` | native; every NaN normalised in keys | [nan-equality](spark-nan-equality.json) |
| `lt`, sorts, `max`, `greatest`, quantiles | `nan_order` | `GREATEST` | native | [nan-order](spark-nan-order.json) |
| `equal`, sorts, grouping, `min`, `max` (`fp64`) | `zero_sign` | `ONE_ZERO` | equal; grouping normalises to 0.0; `min`, `max`, sorts keep the first zero | [zero-order](spark-zero-order.json) |
| doubles | `nan_kind` | `ONE_NAN` | the sign survives `-x`; created NaN negative on x86-64 | [nan-sign](spark-nan-sign.json) |
| sort key | `null_order` | as the key states | `NULLS FIRST` ascending, `NULLS LAST` descending by default; both honoured | [null-order](spark-null-order.json) |
| sort, `fetch` | `tie_order` | any order | ties in partition order, varying between runs | [sort-stability](spark-sort-stability.json) |
| sort key | `clustered` | equal keys adjacent | `CLUSTER BY` | [clustered](spark-clustered.json) |
| `aggregate` keys, joins | NULL keys | one group; `=` skips NULL | native; `<=>`, `IS NOT DISTINCT FROM` | [null-keys](spark-null-keys.json) |
| `and`, `or`, `not`, `bool_and`, `bool_or` | | Kleene; aggregates skip NULLs | native | [kleene](spark-kleene.json) |
| `first`, `last`, `mode`, `arg_min`, `arg_max` | `tie_pick` | any row | arrival order; `mode` any of a tie | [first-last](spark-first-last.json) |
| `string_agg`, `array_agg` | `tie_order` | any order | arrival order | first-last |
| `rank`, `ntile`, `percent_rank`, `cume_dist` | `ntile_spread`, `tie_order` | SQL's; NULLs ranked | native | [rank](spark-rank.json) |
| `lag`, `first_value`, windowed sums | frame, `tie_order` | the window's | SQL's default frame, native | [window-values](spark-window-values.json) |
| `UNION`, `INTERSECT`, `EXCEPT` | | NULLs equal | native, `ALL` forms too | [set-operations](spark-set-operations.json) |

### Strings, dates, casts and lists

| Function (types) | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `upper`, `lower` | `char_set` | `UTF8`, full mappings | native, in the JVM's default locale | [case](spark-case.json) |
| `like`, `starts_with`, `strpos`, `replace` | `case_sensitivity` | `CASE_SENSITIVE` | native | [match-functions](spark-match-functions.json) |
| `substring` | `negative_start` | `WRAP_FROM_END`, 1-based | native but a start of 0, which reads as 1 | [substring](spark-substring.json) |
| | `substring_range` | raise outside `[-2³², 2³²)` | `INT` positions: raise from 2³¹ on; off: wrap | [substring-range](spark-substring-range.json) |
| `strpos` | `string_positions` | 1-based characters, 0 when absent | native (`instr`) | [strpos](spark-strpos.json) |
| `character_length`, `reverse`, `btrim` | | code points; spaces | native | [string-plain](spark-string-plain.json) |
| `str_concat` | `null_handling` | `ACCEPT_NULLS` | native; `concat_ws` skips NULLs | [concat](spark-concat.json) |
| `regexp_extract`, `regexp_replace` | `regex_dialect` | RE2; `''` without a match | `java.util.regex`, ASCII classes, `$1`; `''` without a match | [regex](spark-regex.json) |
| `md5`, `sha256` | `digests` | hex of the UTF-8 bytes | native (`sha2(s, 256)`) | [digests](spark-digests.json) |
| date and timestamp arithmetic | `date_range` | raise outside 0001 … 9999 | computes past them; `date_add` wraps at 2³¹ days ([SP-2](../../../upstream/bugs/SP-2.json)); a bare `long overflow` at the end of the timestamp range ([SP-3](../../../upstream/bugs/SP-3.json)) | [date-range](spark-date-range.json) |
| `TIME ± INTERVAL` | `time_interval_months` | refused | `TIME` off by default; with it, raises past midnight | [time-type](spark-time-type.json) |
| timestamps | precision | microseconds | native | [timestamp-precision](spark-timestamp-precision.json) |
| time zones | | outside the model | session zone; gaps forward, overlaps earlier | [time-zones](spark-time-zones.json) |
| `date_part`, `date_trunc` | `week_numbering` | ISO weeks, floor before 1970 | native; `dayofweek` counts from Sunday | [week-parts](spark-week-parts.json) |
| `cast` `fp64` → integer | `float_to_int`, `cast_failure` | `TRUNCATE`, raise | native; off: saturate (`INT`, `BIGINT`) or wrap | [cast-double-to-int](spark-cast-double-to-int.json) |
| `cast` from and to strings | parsing, formatting | the reference's rules | lenient parsing (trims, hex floats, `1.5d`); Java's double text | [cast-string](spark-cast-string.json) |
| `cast` with `RETURN_NULL` | `try_variants` | NULL on failure | `try_cast`, and `try_*` for arithmetic | [try-variants](spark-try-variants.json) |
| `<` and sorts of lists | `list_null_order` | NULL in `<`, `GREATEST` in sorts | a NULL element lowest in both | [list-order](spark-list-order.json) |
| `list_extract` | indexing | 1-based | `element_at` 1-based, 0 raises; `[]` 0-based | [list-index](spark-list-index.json) |
| `=` on structs and lists | | structural, NULLs equal | native | [nested-equality](spark-nested-equality.json) |
| `UNNEST` | NULL and empty lists | no row | native (`explode`) | [explode](spark-explode.json) |

### Execution, frontend and I/O

| Construct | Option | Reference | Spark | Fact |
|---|---|---|---|---|
| `CASE`, `AND`, filters | `evaluation_order` | a branch sees only its rows | `CASE`, `IF`, `COALESCE` lazy; `AND`, `OR` short-circuit left to right; pushdown only removes raises | [exec-evaluation-order](spark-exec-evaluation-order.json) |
| extra raises | `raise_set` | D2 | `INT` positions, ANSI string coercion, `element_at(…, 0)`, regexes, week patterns; two errors without a class | [raise-set](spark-raise-set.json) |
| settings | | none | ANSI, timestamp type, time zone, legacy statistics, decimal precision loss, `TIME`, the JVM locale | [exec-settings](spark-exec-settings.json) |
| parallelism | | bags; open orders | double sums, `BIGINT` sum overflow, `first`, ties vary with partitioning | [exec-parallel](spark-exec-parallel.json) |
| platform | | black-box libm, one NaN | `Math` intrinsics, NaN sign, locale | [exec-platform](spark-exec-platform.json) |
| sizes | | decimals to 38 digits | decimals to 38; strings and arrays below 2³¹ | [exec-size-limits](spark-exec-size-limits.json) |
| streaming | | none | batch only | [exec-streaming-fallback](spark-exec-streaming-fallback.json) |
| types | names, implicit casts, literals | explicit in the plan | Spark's names; ANSI precedence; `INT` literals, `1.5` a decimal | [type-names](spark-type-names.json), [implicit-casts](spark-implicit-casts.json), [literal-types](spark-literal-types.json) |
| I/O | formats, object stores, catalogs | outside the plan | Parquet, ORC, CSV, JSON, Avro; Hadoop connectors; catalog plugins | [io](spark-io.json) |

## Evidence, fact by fact

The strongest check behind each fact (`evidence`, in the order docs < source
< engine_test < probe < fuzz < proof), the cases of Spark's tests it links,
and for an open deviation the fuzzed results that came out as it says. Of
the 70 facts, 36 rest on fuzzing, 32 on probes, one on Spark's tests
([io](spark-io.json)) and one on the source
([exec-streaming-fallback](spark-exec-streaming-fallback.json)); 59
link cases of Spark's tests, and the other 11 say why none fits.

| Fact | Status | Evidence | Spark's tests | Fuzz |
|---|---|---|---|---|
| [avg-double](spark-avg-double.json) | open | fuzz | 4 cases | 2880 of 2880 |
| [avg-int](spark-avg-int.json) | open | fuzz | 6 cases | 164 of 164 |
| [case](spark-case.json) | no-finding | probe | 2 cases | — |
| [cast-double-to-int](spark-cast-double-to-int.json) | no-finding | probe | 7 cases | — |
| [cast-string](spark-cast-string.json) | open | fuzz | 12 cases | 4962 of 4962 |
| [clustered](spark-clustered.json) | no-finding | probe | none: the suite sorts the rows of a query without `ORDER BY`, so no case shows adjacency | — |
| [concat](spark-concat.json) | no-finding | probe | 3 cases | — |
| [corr](spark-corr.json) | open | fuzz | 5 cases | 204 of 204 |
| [covar](spark-covar.json) | open | fuzz | 2 cases | 408 of 408 |
| [date-range](spark-date-range.json) | open | fuzz | 8 cases | 3360 of 3360 |
| [decimal-arith](spark-decimal-arith.json) | no-finding | probe | 10 cases | — |
| [decimal-negate](spark-decimal-negate.json) | open | fuzz | none: no case negates a decimal of more than 34 digits | 7084 of 7084 |
| [digests](spark-digests.json) | no-finding | probe | none: no case has the output of `md5`, `sha1`, `sha2` or `crc32` | — |
| [double-arith](spark-double-arith.json) | open | fuzz | 3 cases | 3600 of 3600 |
| [double-divide](spark-double-divide.json) | open | fuzz | 7 cases | 1200 of 1200 |
| [double-modulus](spark-double-modulus.json) | open | fuzz | none: `%`, `mod` and `pmod` cases are on integers and decimals only | 2380 of 2380 |
| [elem-rounding](spark-elem-rounding.json) | open | fuzz | 5 cases | 12000 of 12000 |
| [exec-evaluation-order](spark-exec-evaluation-order.json) | no-finding | probe | 5 cases | — |
| [exec-parallel](spark-exec-parallel.json) | open | fuzz | none: each query runs once, on one local partitioning | 3902 of 3902 |
| [exec-platform](spark-exec-platform.json) | open | fuzz | 1 cases | 16800 of 16800 |
| [exec-settings](spark-exec-settings.json) | open | fuzz | 7 cases | 17942 of 17942 |
| [exec-size-limits](spark-exec-size-limits.json) | open | fuzz | 3 cases | 964 of 964 |
| [exec-streaming-fallback](spark-exec-streaming-fallback.json) | no-finding | source | none: the SQL tests run batch queries only; source at the tag instead | — |
| [explode](spark-explode.json) | no-finding | probe | 12 cases | — |
| [first-last](spark-first-last.json) | no-finding | probe | 7 cases | — |
| [fp32](spark-fp32.json) | open | fuzz | 6 cases | 5970 of 5970 |
| [implicit-casts](spark-implicit-casts.json) | no-finding | probe | 11 cases | — |
| [int-abs](spark-int-abs.json) | no-finding | probe | 1 cases | — |
| [int-arith](spark-int-arith.json) | no-finding | probe | 8 cases | — |
| [int-divide](spark-int-divide.json) | open | fuzz | 8 cases | 9594 of 9594 |
| [int-modulus](spark-int-modulus.json) | no-finding | probe | 6 cases | — |
| [int-pow](spark-int-pow.json) | open | fuzz | none: the `power` cases take doubles only | 1200 of 1200 |
| [int-shift](spark-int-shift.json) | open | fuzz | 5 cases | 14400 of 14400 |
| [io](spark-io.json) | no-finding | engine_test | 6 cases | — |
| [kleene](spark-kleene.json) | no-finding | probe | 9 cases | — |
| [list-index](spark-list-index.json) | open | fuzz | 13 cases | 6326 of 6326 |
| [list-order](spark-list-order.json) | open | fuzz | 1 cases | 8400 of 8400 |
| [literal-types](spark-literal-types.json) | no-finding | probe | 10 cases | — |
| [match-functions](spark-match-functions.json) | no-finding | probe | 6 cases | — |
| [math-domain](spark-math-domain.json) | open | fuzz | none: no `ln(0)`, `sqrt(-1)`, `asin(2)` or `atan2(0, 0)` case | 10800 of 10800 |
| [nan-equality](spark-nan-equality.json) | no-finding | probe | 3 cases | — |
| [nan-order](spark-nan-order.json) | no-finding | probe | 3 cases | — |
| [nan-sign](spark-nan-sign.json) | open | fuzz | none: no case looks at a NaN's sign bit | 4800 of 4800 |
| [nested-equality](spark-nested-equality.json) | no-finding | probe | 2 cases | — |
| [nonfinite-aggregates](spark-nonfinite-aggregates.json) | open | fuzz | 5 cases | 820 of 820 |
| [null-keys](spark-null-keys.json) | no-finding | probe | 4 cases | — |
| [null-order](spark-null-order.json) | no-finding | probe | 5 cases | — |
| [quantile](spark-quantile.json) | open | fuzz | 5 cases | 2244 of 2244 |
| [raise-set](spark-raise-set.json) | open | fuzz | 13 cases | 25384 of 25384 |
| [rank](spark-rank.json) | no-finding | probe | 7 cases | — |
| [regex](spark-regex.json) | open | fuzz | 6 cases | 3600 of 3600 |
| [round](spark-round.json) | open | fuzz | 7 cases | 11956 of 11956 |
| [set-operations](spark-set-operations.json) | no-finding | probe | 7 cases | — |
| [sort-stability](spark-sort-stability.json) | no-finding | probe | none: the suite sorts unordered output and runs each query once | — |
| [string-plain](spark-string-plain.json) | no-finding | probe | 5 cases | — |
| [strpos](spark-strpos.json) | no-finding | probe | 14 cases | — |
| [substring-range](spark-substring-range.json) | open | fuzz | 2 cases | 794 of 794 |
| [substring](spark-substring.json) | open | fuzz | 4 cases | 1200 of 1200 |
| [sum-double](spark-sum-double.json) | open | fuzz | 2 cases | 2880 of 2880 |
| [sum-int](spark-sum-int.json) | open | fuzz | 7 cases | 1022 of 1022 |
| [time-type](spark-time-type.json) | no-finding | probe | 2 cases | — |
| [time-zones](spark-time-zones.json) | no-finding | probe | 4 cases | — |
| [timestamp-precision](spark-timestamp-precision.json) | no-finding | probe | 10 cases | — |
| [try-variants](spark-try-variants.json) | open | fuzz | 13 cases | 7200 of 7200 |
| [type-names](spark-type-names.json) | no-finding | probe | 9 cases | — |
| [var-stddev](spark-var-stddev.json) | open | fuzz | 6 cases | 1440 of 1440 |
| [week-parts](spark-week-parts.json) | no-finding | probe | 10 cases | — |
| [window-values](spark-window-values.json) | no-finding | probe | 7 cases | — |
| [zero-order](spark-zero-order.json) | open | fuzz | none: every `-0.0` in the suite is a decimal literal, 0.0 before it is a double | 5784 of 5784 |
| [zero-sign](spark-zero-sign.json) | open | fuzz | 2 cases | 7042 of 7042 |
